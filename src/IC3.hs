-- IC3 with implicit predicate abstraction
module IC3 (ic3, Proof, Counterexample, Invariant) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State

import Logic
import TransitionSystem

import Z3.Monad

-- Cube is a conjunction of literals
-- Frame consists of blocked cubes
type Cube = [Lit]
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
ic3 :: TransitionSystem -> IO Proof
ic3 ts = evalZ3 $ evalStateT ic3' env where

    -- Perform the IC3
    -- Detect reachability of an error state in one step via `bad` state.
    -- Try recursively blocking the `bad` predecessor.
    -- (1) if blocking succeeded propagate blocked cubes.
    -- (2) if the chain of predecessors reaches the initial frame,
    --     check if the error is real (in a BMC-like style).
    --     (a) report it if so.
    --     (b) otherwise compute interpolants and refine abstraction.
    ic3' :: MonadZ3 z3 => StateT Env z3 Proof
    ic3' = init >> loop' (loop'' (bad >>= block) >> prop)

    -- Initial environment
    env :: Env
    env = Env ts []

    -- Activation variable for the transition relation
    tM :: MonadZ3 z3 => z3 AST
    tM = mkFreshBoolVar "t"

    -- Activation variable for the negated property
    nM :: MonadZ3 z3 => z3 AST
    nM = mkFreshBoolVar "n"

    -- Initial step
    -- Declare the transition relation and the property
    init :: MonadZ3 z3 => StateT Env z3 ()
    init = do
        lift $ do
            t <- tM
            n <- nM
            assert =<< mkIff t =<< mkTrue -- assert t iff trans
            assert =<< mkIff n =<< mkNot =<< mkFalse -- assert n iff not p
        pushNewFrame

    -- Find a predecessor of an error state if one exists.
    bad :: (MonadTrans t, MonadZ3 z3) => ExceptT () (t (StateT Env z3)) Cube
    bad = mapExceptT lift $ do
        lift $ do
            s <- get

            pushNewFrame -- utter nonsense, just debugging

            let ts       = getTransitionSystem s
            let fs@(f:_) = getFrames s
            let t        = getTrans ts
            let p        = getProp ts

            lift $ modelTemp $ when (length fs == 3) $ assert =<< mkFalse -- debugging, replace with actual query for a model

        >>= \r -> case r of
            (Sat, Just m) -> return []
            (Unsat, _) -> throwE () -- there is none
            otherwise -> error "failed to check for bad state"

    -- Try recursively blocking the bad cube
    -- May fail to block
    -- Then if the cex is real, it is returned
    -- Otherwise the abstraction is refined
    block :: MonadZ3 z3 => Cube -> ExceptT () (ExceptT Counterexample (StateT Env z3)) ()
    block c = lift $ do
        r <- lift $ lift check
        case r of
            Sat -> return () -- blocked or abs refined
            Unsat -> throwE $ Counterexample [] -- real error
            otherwise -> error "failed to check if bad state is blocked / refine abstraction"

    -- Propagate blocked cubes to higher frames
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
    loop :: Monad m => ExceptT r m () -> m r
    loop = liftM (either id id) . runExceptT . forever

    loop' :: Monad m => ExceptT a (ExceptT e m) () -> m (Either e a)
    loop' = runExceptT . loop

    loop'' :: (MonadTrans t, Monad m) => ExceptT r m () -> t m r
    loop'' = lift . loop

    temp :: MonadZ3 z3 => z3 a -> z3 () -> z3 a
    temp a b = push >> b >> a >>= \r -> pop 1 >> return r

    checkTemp :: MonadZ3 z3 => z3 () -> z3 Result
    checkTemp = temp check

    modelTemp :: MonadZ3 z3 => z3 () -> z3 (Result, Maybe Model)
    modelTemp = temp getModel
