-- IC3 with implicit predicate abstraction
--
-- Iteratively computes sets of states reachable in 0, 1, ... k steps (via a transition relation)
-- starting in the initial set of states. Tries to prove that the desired property holds in all
-- executions by showing unreachability of a state that violates the property.
--
-- Invariants of the IC3 algorithm:
--   F0 = I
--   Fi => Fi+1             -- moreover, as Fi are sets of blocked cubes, Fi+1 is subset of Fi. This can be checked syntactically.
--   Fi and T implies Fi+1'
--   Fi => P
--
-- Because Fi are ordered by subset relation, each cube c is remembered only in the highest Fk where it is blocked.
-- Thus the true Fi will be represented in fact with: Fi and Fi+1 and Fi+2 and ...
--
-- The algorithm proceeds as follows:
--   1) Get a predecessor of an error state
--     a) if there is none, proceed to 3
--   2) Recursively block the predecessor
--     a) Fails to block
--        i) The error is real, report it - program unsafe.
--       ii) The error is spurious, refine abstraction, go to 1
--     b) Succeeds to block, go to 1
--   3) Propagate blocked cubes to the highest frame Fk possible (as long as the cube is inductive with respect to the frame)
--     a) Fixpoint found, report invariant - program safe.
--     b) Otherwise go to 1
--
-- The algorithm has found a fixpoint when Fi = Fi+1 at the end of some major iteration.
-- In that case Fi and T => Fi, in other words Fi is an invariant:
--   a)  Initiation: I = F0 => F1 => ... Fi, i.e. I => Fi
--   b)  Consecution: Fi and T => Fi+1' = Fi, i.e. Fi and T => Fi'
--   b') Strengthened consecution: Fi and P and T => Fi'
-- In our encoding the check whether Fi = Fi+1 reduces to checking emptiness of Fi.
-- If Fi is a superset of Fi+1, but contains no blocked cube on top of what Fi+1 does.
--
-- Whenever a cube is being blocked, it is first generalized.
--
-- Refinement is achieved with interpolation of a spurious counterexample trace formula.
--
-- Most of the transition system is immutable (initial states, transition relation, property).
-- These are precise and need no refinement, therefore, they are added into the solver context once at the beginning.
--
--   i => I
--   t => T
--   n => not P'
--
-- Whenever a spurious error is encountered (due to a too coarse abstraction).
-- The counterexample trace is interpolated and new predicates are extracted from the interpolants.
-- Each new predicate is assigned two new fresh variables pi, pi' and the following is asserted.
--
--   pi  <=> Predi
--   pi' <=> Predi'
--
-- Thus pi and pi' inherit values depending on the actual queries.
--
module IC3 where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import qualified ListT as L
import qualified Data.Traversable as T
import Data.List
import Debug.Trace

import Z3.Monad

import Logic
import Proof
import qualified Environment as E
import qualified TransitionSystem as TS

-- IC3
-- Given a transition system and a solver to use
-- it attempts to decide whether the system is safe.
-- It returns either a counterexample as a witness of unsafety
-- or an invariant as a certificate of safety.
ic3 :: TS.TransitionSystem -> L.ListT Z3 Proof
ic3 ts = ic3' =<< lift env where

    -- Restart the IC3 after a counterexample is found.
    -- By keeping the work that IC3 has done so far, and
    -- blocking the latest counterexample, we can countinue
    -- until an invariant is found, thus enumerating multiple
    -- counterexamples.
    ic3' :: E.Env -> L.ListT Z3 Proof
    ic3' env = do
        (p, env') <- run env ic3''
        case p of
            cex@(Left  _) -> L.cons cex (ic3' env')
            inv@(Right _) -> return inv

    -- Perform the IC3
    -- Detect reachability of an error state in one step via `bad` state.
    -- Try recursively blocking the `bad` predecessor.
    -- (1) if blocking succeeded propagate blocked cubes.
    -- (2) if the chain of predecessors reaches the initial frame,
    --     check if the error is real (in a BMC-like style).
    --     (a) report it if so.
    --     (b) otherwise compute interpolants and refine abstraction.
    ic3'' :: ProofBranch Counterexample Invariant
    ic3'' = init >> loop (loop' (bad >>= block) >> prop)

    -- Initial environment
    -- These steps are done once and they are not executed when ic3 is restarted on the same input.
    -- Initially there is one empty frame.
    -- The initial set of abstraction predicates is extracted from i, t, and p.
    env :: Z3 E.Env
    env = do
        let i = TS.getInit  ts
            t = TS.getTrans ts
            p = TS.getProp  ts

        -- Extract unique predicates from i, t, and p.
        -- Allocate a new variable for each.
        predDefs <- fmap (map head . group . sort . concat) $ T.sequence $ map getPreds [i, t, p]
        predVars <- let n = length predDefs in T.sequence $ map (\i -> mkBoolVar =<< mkStringSymbol ('p' : '!' : show i)) [0 .. n - 1]

        return $ E.Env ts [[]] (zip predVars predDefs)

    -- Initial step
    -- Declare the transition relation and the property
    init :: ProofBranch Counterexample ()
    init = do
        i  <- getInit
        t  <- getTrans
        p  <- getProp
        ps <- getAbsPreds

        tl <- tM
        nl <- nM

        r <- temp $ do
            assert i
            assert =<< mkNot p
            getModel

        assert =<< mkImplies nl =<< mkNot =<< next p
        assert =<< mkImplies tl t
        mapM assert =<< mapM (uncurry mkIff) ps

        case r of
            (Sat, Just m) -> ProofBranchT $ throwE $ Counterexample []
            (Unsat,    _) -> return ()

    -- Find a predecessor of an error state if one exists.
    -- Find a model of all pi under the assumption Fi and T and not P'.
    -- These are the assignments to the abstraction predicates in the pre-state.
    bad :: MaybeDisproof E.Cube
    bad = do
        fs@(f : _) <- getFrames
        ps         <- getAbsPreds

        pushNewFrame -- debug

        r <- temp $ do
            assert =<< mkAnd =<< T.sequence [ tM, nM ]
            assert =<< mkTrue
            getModel

        case r of
            (Sat, Just m) -> buildCube m (map fst ps)
            (Unsat,    _) -> MaybeDisproof $ throwE ()

    -- Try recursively blocking the bad cube (error predecessor state).
    -- (1) Blocking fails due to reaching F0 with a proof obligation.
    --   (a) Then if the cex is real, it is returned.
    --   (b) Otherwise the abstraction is refined.
    -- (2) Blocking succeeds.
    block :: E.Cube -> MaybeDisproof ()
    block c = block' c =<< getFrames

    block' :: E.Cube -> E.Frames -> MaybeDisproof ()
    block' c (f:fs) = do
        r <- check
        r <- return Unsat
        case r of
            Sat   -> return () -- blocked
            Unsat -> if length fs == 0
                then do
                    MaybeDisproof $ lift $ ProofBranchT $ throwE $ Counterexample [c]
                else
                    block' c fs -- block the counterexample to induction

    -- Propagate blocked cubes to higher frames.
    -- If the constraint corresponding to a blocked cube is inductive with respect to the current frame,
    -- we can move it to the next frame.
    -- (1) If in the end the last two frames are equal (i.e. Fn-1 is empty) then we cannot discover anything
    --     more in the next iteration and thus we have encountered a fixpoint and we can terminate.
    --     Because Fn holds in the prefix and all hypothetical successors it is an invariant of the system.
    -- (2) Else we continue.
    prop :: MaybeProof ()
    prop = do
        pushNewFrame

        fs@(f : f' : _) <- getFrames

        -- TODO: propagate

        if length f' == 0
        then MaybeProof $ throwE $ Invariant []
        else return ()

    --gen :: E.Cube -> MaybeDisproof

    -- Activation variable for the initial states
    iM :: MonadZ3 z3 => z3 AST
    iM = mkBoolVar =<< mkStringSymbol "i"

    -- Activation variable for the transition relation
    tM :: MonadZ3 z3 => z3 AST
    tM = mkBoolVar =<< mkStringSymbol "t"

    -- Activation variable for the negated property
    nM :: MonadZ3 z3 => z3 AST
    nM = mkBoolVar =<< mkStringSymbol "n"

    -- Auxiliary functions
    loop :: MaybeProof () -> ProofBranch Counterexample Invariant
    loop = liftM (either id id) . runExceptT . runProof . forever

    loop' :: MaybeDisproof () -> MaybeProof ()
    loop' = MaybeProof . lift . liftM (either id id) . runExceptT . runDisproof . forever
