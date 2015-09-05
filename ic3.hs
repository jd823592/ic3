-- IC3 with implicit predicate abstraction
module IC3 where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State

import Logic
import Solver
import TransitionSystem

-- Cube is a conjunction of literals
-- Frame consists of blocked cubes
type Cube = [Lit]
type Frame = [Cube]
type Frames = [Frame]

type Step = Int

data Env = Env { getTransitionSystem :: TransitionSystem, getSolver :: Solver, getFrames :: Frames }

data Counterexample = Counterexample [Step] deriving Show
data Invariant = Invariant Frame deriving Show

type Result = Either Counterexample Invariant

-- IC3
-- Given a transition system and a solver to use
-- it attempts to decide whether the system is safe.
-- It returns either a counterexample as a witness of unsafety
-- or an invariant as a certificate of safety.
ic3 :: TransitionSystem -> Solver -> IO Result
ic3 ts s = evalStateT ic3' env where

    -- Perform the IC3
    -- Detect reachability of an error state in one step via `bad` state.
    -- Try recursively blocking the `bad` predecessor.
    -- (1) if blocking succeeded propagate blocked cubes.
    -- (2) if the chain of predecessors reaches the initial frame,
    --     check if the error is real (in a BMC-like style).
    --     (a) report it if so.
    --     (b) otherwise compute interpolants and refine abstraction.
    ic3' :: StateT Env IO Result
    ic3' = init >> loop' (loop'' (bad >>= block) >> prop)

    -- Initial environment
    env :: Env
    env = Env ts s []

    -- Initial step
    init :: StateT Env IO ()
    init = do
        pushNewFrame

    -- Find a predecessor of an error state if one exists.
    bad :: MonadTrans t => ExceptT () (t (StateT Env IO)) Cube
    bad = mapExceptT lift $ do
        line <- lift $ lift getLine
        if length line == 0
        then return []
        else throwE () -- there is none

    -- Try recursively blocking the bad cube
    -- May fail to block
    -- Then if the cex is real, it is returned
    -- Otherwise the abstraction is refined
    block :: Cube -> ExceptT () (ExceptT Counterexample (StateT Env IO)) ()
    block c = lift $ do
        line <- lift $ lift getLine
        if length line == 0
        then return () -- blocked or abs refined
        else throwE $ Counterexample [] -- real error

    -- Propagate blocked cubes to higher frames
    prop :: MonadTrans t => ExceptT Invariant (t (StateT Env IO)) ()
    prop = mapExceptT lift $ do
        line <- lift $ lift getLine
        if length line == 0
        then return () -- no fixpoint yet
        else throwE $ Invariant [] -- fixpoint

    -- Push a new frame
    pushNewFrame :: StateT Env IO ()
    pushNewFrame = do
        env <- get
        put $ Env (getTransitionSystem env) (getSolver env) ([] : getFrames env)

    -- Auxiliary functions
    loop :: Monad m => ExceptT r m () -> m r
    loop = liftM (either id id) . runExceptT . forever

    loop' :: Monad m => ExceptT a (ExceptT e m) () -> m (Either e a)
    loop' = runExceptT . loop

    loop'' :: (MonadTrans t, Monad m) => ExceptT r m () -> t m r
    loop'' = lift . loop
