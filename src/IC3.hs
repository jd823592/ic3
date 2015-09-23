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
import Control.Monad.Extra
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.List
import qualified Data.List.Zipper as Z
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
        predDefs <- fmap (nub . concat) $ T.sequence $ map getStatePreds [i, t, p]
        predVars <- let n = length predDefs in T.sequence $ map (\i -> mkBoolVar =<< mkStringSymbol ('p' : '!' : show i)) [0 .. n - 1]

        return $ E.Env ts (Z.fromList [[]]) (zip predVars predDefs)

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
ic3core :: ProofBranch Proof a
ic3core = init >> loop (bad >>= block <|> prop) where
    init :: ProofBranch Proof ()
    init = do
        i  <- getInit
        il <- getInitL
        t  <- getTrans
        tl <- getTransL
        p  <- getProp
        nl <- getPropL
        ps <- getAbsPreds

        r <- temp $ do
            assert i
            assert =<< mkNot p
            getModel

        assert =<< mkImplies il i
        assert =<< mkImplies tl t
        assert =<< mkImplies nl =<< mkNot =<< next p
        mapM assert =<< mapM (uncurry mkIff) ps
        mapM assert =<< mapM (next <=< uncurry mkIff) ps

        case r of
            (Sat, Just m) -> ProofBranchT . throwE . Left . Counterexample . return =<< buildCube m (map fst ps)
            (Unsat,    _) -> return ()

    loop :: Monad m => m a -> m b
    loop = forever

    -- Find cube of states that may reach an error state in one step.
    bad :: ProofBranch Proof (Maybe E.Cube)
    bad = do
        f  <- getFrame
        ps <- getAbsPreds

        r <- temp $ do
            assert =<< mkAnd =<< mapM (mkNot <=< mkAnd) f           -- Fn
            assert =<< mkAnd =<< T.sequence [ getTransL, getPropL ] -- T, not P'
            getModel

        case r of
            (Sat, Just m) -> fmap Just $ buildCube m (map fst ps)
            (Unsat,    _) -> return Nothing

    -- Try recursively blocking the bad cube (error predecessor state).
    -- If blocking fails due to reaching F0 with a proof obligation, if
    --   (a) the cex is real, it is returned,
    --   (b) otherwise the abstraction is refined.
    block :: E.Cube -> ProofBranch Counterexample ()
    block c = block' [c] where
        block' :: E.Cubes -> ProofBranch Counterexample ()
        block' cs@(c : _) = do
            bot <- isBotFrame

            if bot
            then do
                r <- temp $ do
                    assert =<< getInitL -- I
                    checkCube c         -- c
                case r of
                    (Unsat, Right k) -> frameUpd (k :) -- blocked
                    (Sat,    Left _) -> do
                        exp <- getAbsPreds
                        frameUpd (c :)
                        frameTop
                        ProofBranchT . throwE . Counterexample =<< mapM (expandCube exp) cs
            else do
                frameBwd
                r <- isInductive c
                frameFwd
                case r of
                    (True, _) -> frameUpd (c :) -- blocked
                    (False, Left c') -> do
                        frameBwd
                        block' (c' : cs) -- 1. block current predecessor (counterexample to induction) in lower frame
                        frameFwd
                        block' cs        -- 2. block any other predecessor

    -- Propagate inductive blocked cubes to higher frames.
    -- When two consecutive frames are equal, we have reached a safe fixpoint and can stop.
    prop :: ProofBranch Invariant ()
    prop = do
        pushNewFrame
        frameBot
        prop' []

        f' <- getPrevFrame

        when (length f' == 0) $ do
            exp <- getAbsPreds
            ProofBranchT . throwE . Invariant =<< mapM (expandCube exp) =<< getFrame where

        prop' :: E.Cubes -> ProofBranch Invariant E.Cubes
        prop' ic = do
            frameFwd
            frameUpd (nub . (ic ++))

            top <- isTopFrame

            if top
            then return []
            else do
                (ic', f') <- partitionM (fmap fst . isInductive) =<< getFrame
                frameUpd (\_ -> f')
                prop' ic'

    isInductive :: MonadProofState m => E.Cube -> m (Bool, Either E.Cube E.Cube)
    isInductive c = temp $ do
        c' <- mapM next c

        assert =<< mkAnd =<< mapM (mkAnd <=< (mapM (mkNot <=< mkAnd))) =<< getFramesUp -- Fi ... Fn
        assert =<< mkNot =<< mkAnd c                                                   -- not c
        assert =<< getTransL                                                           -- T
        (r, w) <- checkCube c'                                                         -- c'

        return (r == Unsat, w)

    checkCube :: MonadProofState m => E.Cube -> m (Result, Either E.Cube E.Cube)
    checkCube c = do
        r <- checkAssumptions c

        case r of
            Sat -> do
                (_, Just m) <- getModel
                k <- buildCube m =<< fmap (map fst) getAbsPreds
                return (r, Left k)
            Unsat -> do
                k <- mapM untime =<< getUnsatCore
                return (r, Right k)

    (<|>) :: (d -> ProofBranch a c) -> ProofBranch b c -> Maybe d -> ProofBranch (Either a b) c
    (<|>) l _ (Just d) = mapL Left (l d)
    (<|>) _ r _        = mapL Right r

    mapL :: (a -> c) -> ProofBranch a b -> ProofBranch c b
    mapL f = ProofBranchT . ExceptT . fmap (either (Left . f) Right) . runExceptT . runProofBranchT
