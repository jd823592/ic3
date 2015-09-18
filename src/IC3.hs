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
import Control.Monad.Trans.State
import Data.List
import qualified Data.Traversable as T
import qualified ListT as L

import Z3.Monad

import Logic
import Proof
import qualified Environment as E
import qualified TransitionSystem as TS

-- IC3
-- Given a transition system and a solver to use
-- it returns either a counterexample as a witness of unsafety
-- or an invariant as a certificate of safety of the system.
ic3 :: TS.TransitionSystem -> L.ListT Z3 Proof
ic3 ts = ic3enum =<< lift env where
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

-- Keep enumerating counterexamples
ic3enum :: E.Env -> L.ListT Z3 Proof
ic3enum env = do
    (p, env') <- runic3 env ic3core
    case p of
        cex@(Left  _) -> L.cons cex (ic3enum env')
        inv@(Right _) -> return inv

runic3 :: E.Env -> ProofBranch Proof Proof -> L.ListT Z3 (Proof, E.Env)
runic3 env = lift . (`runStateT` env) . runProofStateT . fmap (either id id) . runExceptT . runProofBranchT

-- IC3
ic3core :: ProofBranch Proof Proof
ic3core = init >> loop (bad >>= block <|> prop) where
    init :: ProofBranch Proof ()
    init = do
        i  <- getInit
        t  <- getTrans
        tl <- getTransL
        p  <- getProp
        nl <- getPropL
        ps <- getAbsPreds

        r <- temp $ do
            assert i
            assert =<< mkNot p
            getModel

        assert =<< mkImplies nl =<< mkNot =<< next p
        assert =<< mkImplies tl t
        mapM assert =<< mapM (uncurry mkIff) ps

        case r of
            (Sat, Just m) -> ProofBranchT . throwE . Left . Counterexample . (:[]) =<< buildCube m (map fst ps)
            (Unsat,    _) -> return ()

    loop :: Monad m => m a -> m b
    loop = forever

    -- Find cube of states that may reach an error state in one step.
    bad :: ProofBranch Proof (Maybe E.Cube)
    bad = do
        fs@(f : _) <- getFrames
        ps         <- getAbsPreds

        r <- temp $ do
            assert =<< mkAnd =<< T.sequence [ getTransL, getPropL ]
            assert =<< mkTrue
            getModel

        case r of
            (Sat, Just m) -> fmap Just $ buildCube m (map fst ps)
            (Unsat,    _) -> return Nothing

    -- Try recursively blocking the bad cube (error predecessor state).
    -- If blocking fails due to reaching F0 with a proof obligation, if
    --   (a) the cex is real, it is returned,
    --   (b) otherwise the abstraction is refined.
    block :: E.Cube -> ProofBranch Counterexample ()
    block c = block' c =<< getFrames where
        block' :: E.Cube -> E.Frames -> ProofBranch Counterexample ()
        block' c (f : fs) = do
            r <- check
            case r of
                Sat   -> return () -- blocked
                Unsat -> if length fs == 0
                    then do
                        exp <- getAbsPreds
                        ProofBranchT . throwE . Counterexample =<< mapM (expandCube exp) [c]
                    else
                        block' c fs -- block the counterexample to induction

    -- Propagate inductive blocked cubes to higher frames.
    -- When two consecutive frames are equal, we have reached a safe fixpoint and can stop.
    prop :: ProofBranch Invariant ()
    prop = do
        pushNewFrame

        fs@(f : f' : _) <- getFrames

        -- TODO: propagate

        if length f' == 0
        then ProofBranchT . throwE $ Invariant []
        else return ()

    (<|>) :: (d -> ProofBranch a c) -> ProofBranch b c -> Maybe d -> ProofBranch (Either a b) c
    (<|>) l r m = case m of
        Just d  -> mapL Left (l d)
        Nothing -> mapL Right r

    mapL :: (a -> c) -> ProofBranch a b -> ProofBranch c b
    mapL f = ProofBranchT . ExceptT . fmap (either (Left . f) Right) . runExceptT . runProofBranchT
