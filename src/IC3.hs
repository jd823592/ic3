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
module IC3 (ic3, Proof) where

import System.IO.Unsafe (unsafeInterleaveIO)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import qualified Data.Traversable as T

import Logic
import TransitionSystem

import Z3.Monad

-- Cube is a conjunction of literals
-- Frame consists of blocked cubes
type Cube = [Expr]
type Frame = [Cube]
type Frames = [Frame]

type Step = Int

data Env = Env { getTransitionSystem :: TransitionSystem, getFrames :: Frames }

data Counterexample = Counterexample [Step] deriving Show
data Invariant = Invariant Frame deriving Show

type Proof = Either Counterexample Invariant

-- IC3
-- Given a transition system and a solver to use
-- it attempts to decide whether the system is safe.
-- It returns either a counterexample as a witness of unsafety
-- or an invariant as a certificate of safety.
ic3 :: TransitionSystem -> IO [Proof]
ic3 ts = ic3' env where

    -- Restart the IC3 after a counterexample is found.
    -- By keeping the work that IC3 has done so far, and
    -- blocking the latest counterexample, we can countinue
    -- until an invariant is found, thus enumerating multiple
    -- counterexamples.
    ic3' :: Env -> IO [Proof]
    ic3' env = do
        (p, env') <- evalZ3 . (`runStateT` env) . runExceptT $ ic3''
        case p of
            cex@(Left  _) -> unsafeInterleaveIO (ic3' env') >>= return . (cex :)
            inv@(Right _) -> return [inv]

    -- Perform the IC3
    -- Detect reachability of an error state in one step via `bad` state.
    -- Try recursively blocking the `bad` predecessor.
    -- (1) if blocking succeeded propagate blocked cubes.
    -- (2) if the chain of predecessors reaches the initial frame,
    --     check if the error is real (in a BMC-like style).
    --     (a) report it if so.
    --     (b) otherwise compute interpolants and refine abstraction.
    ic3'' :: MonadZ3 z3 => ExceptT Counterexample (StateT Env z3) Invariant
    ic3'' = init >> loop (loop' (bad >>= block) >> prop)

    -- Initial environment
    env :: Env
    env = Env ts []

    -- Initial step
    -- Declare the transition relation and the property
    init :: MonadZ3 z3 => ExceptT Counterexample (StateT Env z3) ()
    init = do
        lift $ do
            s <- get

            let ts = getTransitionSystem s
            let i  = getInit  ts
            let t  = getTrans ts
            let p  = getProp  ts

            -- reset the solver
            -- and do other cleanup necessary to allow reexecution with remembered env
            pushNewFrame

            lift $ do
                tl <- tM
                nl <- nM

                -- assert init and not p
                m <- temp $ do
                    assert =<< toZ3 i
                    assert =<< mkNot =<< toZ3 p
                    getModel

                assert =<< mkImplies nl =<< mkNot =<< toZ3 p -- assert n => not p'
                assert =<< mkImplies tl =<< toZ3 t           -- assert t => trans

                return m

        >>= \r -> case r of
            (Sat, Just m) -> throwE $ Counterexample [] -- init intersects error states
            (Unsat, _) -> return () -- there is no intersection between init and error states
            otherwise -> error "failed to check init"

    -- Find a predecessor of an error state if one exists.
    -- Find a model of all pi under the assumption Fi and T and not P'.
    -- These are the assignments to the abstraction predicates in the pre-state.
    bad :: (MonadTrans t, MonadZ3 z3) => ExceptT () (t (StateT Env z3)) Cube
    bad = mapExceptT lift $ do
        lift $ do
            s <- get

            pushNewFrame -- utter nonsense, just debugging

            let ts       = getTransitionSystem s
            let fs@(f:_) = getFrames s
            let t        = getTrans ts
            let p        = getProp ts

            lift $ temp $ do
                assert =<< mkAnd =<< T.sequence [ tM, nM ]
                when (length fs == 3) $ assert =<< mkFalse -- debugging, replace with actual query for a model
                getModel

        >>= \r -> case r of
            (Sat, Just m) -> return [] -- bad cube found
            (Unsat, _) -> throwE () -- there is none
            otherwise -> error "failed to check bad state"

    -- Activation variable for the initial states
    iM :: MonadZ3 z3 => z3 AST
    iM = mkFreshBoolVar "i"

    -- Activation variable for the transition relation
    tM :: MonadZ3 z3 => z3 AST
    tM = mkFreshBoolVar "t"

    -- Activation variable for the negated property
    nM :: MonadZ3 z3 => z3 AST
    nM = mkFreshBoolVar "n"

    -- Try recursively blocking the bad cube (error predecessor state).
    -- (1) Blocking fails due to reaching F0 with a proof obligation.
    --   (a) Then if the cex is real, it is returned.
    --   (b) Otherwise the abstraction is refined.
    -- (2) Blocking succeeds.
    block :: MonadZ3 z3 => Cube -> ExceptT () (ExceptT Counterexample (StateT Env z3)) ()
    block c = lift $ do
        r <- lift $ lift check
        case r of
            Sat -> return () -- blocked or abs refined
            Unsat -> do
                -- We will report this error, however we can exclude the cube incident with the initial states.
                -- That allows us to continue searching for other errors if we like.
                throwE $ Counterexample [] -- real error
            otherwise -> error "failed to check if bad state is blocked / refine abstraction"

    -- Propagate blocked cubes to higher frames.
    -- If the constraint corresponding to a blocked cube is inductive with respect to the current frame,
    -- we can move it to the next frame.
    -- (1) If in the end the last two frames are equal (i.e. Fn-1 is empty) then we cannot discover anything
    --     more in the next iteration and thus we have encountered a fixpoint and we can terminate.
    --     Because Fn holds in the prefix and all hypothetical successors it is an invariant of the system.
    -- (2) Else we continue.
    prop :: (MonadTrans t, MonadZ3 z3) => ExceptT Invariant (t (StateT Env z3)) ()
    prop = mapExceptT lift $ do
        lift pushNewFrame
        --return () -- no fixpoint yet
        fs <- fmap getFrames $ lift get -- debugging
        throwE $ Invariant $ replicate (length fs) [] -- fixpoint

    -- Push a new frame
    pushNewFrame :: MonadZ3 z3 => StateT Env z3 ()
    pushNewFrame = do
        env <- get
        put $ Env (getTransitionSystem env) ([] : getFrames env)

    -- Auxiliary functions
    loop :: Monad m => ExceptT a m b -> m a
    loop = liftM (either id id) . runExceptT . forever

    loop' :: Monad m => ExceptT () m () -> ExceptT Invariant m ()
    loop' = lift . loop

    temp :: MonadZ3 z3 => z3 a -> z3 a
    temp a = push >> a >>= \r -> pop 1 >> return r
