-- IC3 with implicit predicate abstraction
module IC3 (ic3, Result, Counterexample, Invariant) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State

import Logic
import TransitionSystem

import qualified Z3.Monad as Z3

-- Cube is a conjunction of literals
-- Frame consists of blocked cubes
type Cube = [Lit]
type Frame = [Cube]
type Frames = [Frame]

type Step = Int

data Env = Env { getTransitionSystem :: TransitionSystem, getFrames :: Frames }

data Counterexample = Counterexample [Step] deriving Show
data Invariant = Invariant Frame deriving Show

type Result = Either Counterexample Invariant

-- IC3
-- Given a transition system and a solver to use
-- it attempts to decide whether the system is safe.
-- It returns either a counterexample as a witness of unsafety
-- or an invariant as a certificate of safety.
ic3 :: TransitionSystem -> IO Result
ic3 ts = Z3.evalZ3 $ evalStateT ic3' env where

    -- Perform the IC3
    -- Detect reachability of an error state in one step via `bad` state.
    -- Try recursively blocking the `bad` predecessor.
    -- (1) if blocking succeeded propagate blocked cubes.
    -- (2) if the chain of predecessors reaches the initial frame,
    --     check if the error is real (in a BMC-like style).
    --     (a) report it if so.
    --     (b) otherwise compute interpolants and refine abstraction.
    ic3' :: Z3.MonadZ3 z3 => StateT Env z3 Result
    ic3' = init >> loop' (loop'' (bad >>= block) >> prop)

    -- Initial environment
    env :: Env
    env = Env ts []

    -- Initial step
    init :: Z3.MonadZ3 z3 => StateT Env z3 ()
    init = do
        pushNewFrame

    -- Find a predecessor of an error state if one exists.
    bad :: (MonadTrans t, Z3.MonadZ3 z3) => ExceptT () (t (StateT Env z3)) Cube
    bad = mapExceptT lift $ do
        s <- lift get

        let ts = getTransitionSystem s
        let fs = getFrames s
        let f  = head $ getFrames s
        let t  = getTrans ts
        let p  = getProp ts

        lift $ lift Z3.push

        lift pushNewFrame -- utter nonsense, just debugging

        if length fs == 5
        then lift $ lift $ Z3.mkFalse >>= Z3.solverAssertCnstr
        else return ()

        r <- lift $ lift Z3.check

        lift $ lift $ Z3.pop 1

        case r of
            Z3.Sat -> return []
            Z3.Unsat -> throwE () -- there is none
            otherwise -> error "Z3 failed to check for bad state"

    -- Try recursively blocking the bad cube
    -- May fail to block
    -- Then if the cex is real, it is returned
    -- Otherwise the abstraction is refined
    block :: Z3.MonadZ3 z3 => Cube -> ExceptT () (ExceptT Counterexample (StateT Env z3)) ()
    block c = lift $ do
        r <- lift $ lift Z3.check
        case r of
            Z3.Sat -> return () -- blocked or abs refined
            Z3.Unsat -> throwE $ Counterexample [] -- real error
            otherwise -> error "Z3 failed to check if bad state is blocked / refine abstraction"

    -- Propagate blocked cubes to higher frames
    prop :: (MonadTrans t, Z3.MonadZ3 z3) => ExceptT Invariant (t (StateT Env z3)) ()
    prop = mapExceptT lift $ do
        --return () -- no fixpoint yet
        fs <- fmap getFrames $ lift get -- debugging
        throwE $ Invariant $ replicate (1 + length fs) [Pos $ Var 3] -- fixpoint

    -- Push a new frame
    pushNewFrame :: Z3.MonadZ3 z3 => StateT Env z3 ()
    pushNewFrame = do
        env <- get
        put $ Env (getTransitionSystem env) ([] : getFrames env)

    -- Auxiliary functions
    loop :: Monad m => ExceptT r m () -> m r
    loop = liftM (either id id) . runExceptT . forever

    loop' :: Monad m => ExceptT a (ExceptT e m) () -> m (Either e a)
    loop' = runExceptT . loop

    loop'' :: (MonadTrans t, Monad m) => ExceptT r m () -> t m r
    loop'' = lift . loop
