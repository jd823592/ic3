module Proof where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Data.List
import Z3.Monad

import qualified Data.List.Zipper as Z

import Environment (Env(Env), Cube, Cubes, Frame, Frames, Predicate, Predicates)
import TransitionSystem (Formula)
import qualified Environment as E
import qualified Logic as L
import qualified TransitionSystem as T

class Reportable r where
    stringify :: MonadZ3 m => r -> m String

data Counterexample = Counterexample Cubes
data Invariant = Invariant Frame

instance Reportable AST where
    stringify = astToString

instance Reportable Counterexample where
    stringify (Counterexample cs) = do
        syms <- fmap (intercalate "]; [") (mapM (liftM (intercalate ", ") . mapM stringify) cs)
        return $ "Counterexample [" ++ syms ++ "]"

instance Reportable Invariant where
    stringify (Invariant f) = do
        syms <- fmap (intercalate "]; [") (mapM (liftM (intercalate ", ") . mapM stringify) f)
        return $ "Invariant [" ++ syms ++ "]"

type Proof         = Either Counterexample Invariant
type ProofState    = ProofStateT Z3
type ProofBranch a = ProofBranchT a ProofState

class MonadZ3 m => MonadProofState m where
    getInit      :: m Formula
    getInitL     :: m Formula
    getTrans     :: m Formula
    getTransL    :: m Formula
    getProp      :: m Formula
    getPropL     :: m Formula
    getFrame     :: m Frame
    getPrevFrame :: m Frame
    getFramesUp  :: m Frames
    getAbsPreds  :: m Predicates
    pushNewFrame :: m ()
    frameTop     :: m ()
    frameBot     :: m ()
    frameFwd     :: m ()
    frameBwd     :: m ()
    frameUpd     :: (Frame -> Frame) -> m ()
    isTopFrame   :: m Bool
    isBotFrame   :: m Bool
    temp         :: m a -> m a
    logMsg       :: String -> m ()
    logMsg = liftIO . putStrLn

newtype ProofStateT m a = ProofStateT { runProofStateT :: StateT Env m a }

instance MonadTrans ProofStateT where
    lift = ProofStateT . lift

instance Functor m => Functor (ProofStateT m) where
    fmap f = ProofStateT . (fmap f) . runProofStateT

instance (Functor m, Monad m) => Applicative (ProofStateT m) where
    pure  = return
    (<*>) = ap

instance Monad m => Monad (ProofStateT m) where
    return  = ProofStateT . return
    a >>= b = ProofStateT (runProofStateT a >>= runProofStateT . b)

instance MonadIO m => MonadIO (ProofStateT m) where
    liftIO = lift . liftIO

instance MonadZ3 m => MonadProofState (ProofStateT m) where
    getInit      = ProofStateT $ fmap (T.getInit  . E.getTransitionSystem) get
    getInitL     = ProofStateT . lift $ mkBoolVar =<< mkStringSymbol "i"
    getTrans     = ProofStateT $ fmap (T.getTrans . E.getTransitionSystem) get
    getTransL    = ProofStateT . lift $ mkBoolVar =<< mkStringSymbol "t"
    getProp      = ProofStateT $ fmap (T.getProp  . E.getTransitionSystem) get
    getPropL     = ProofStateT . lift $ mkBoolVar =<< mkStringSymbol "n"
    getFrame     = ProofStateT $ fmap (Z.cursor . E.getFrames) get
    getPrevFrame = ProofStateT $ fmap ((\(Z.Zip _  (_ : p : _)) -> p)        . E.getFrames) get
    getFramesUp  = ProofStateT $ fmap ((\(Z.Zip ls (r : _))     -> (r : ls)) . E.getFrames) get
    getAbsPreds  = ProofStateT $ fmap E.getAbsPreds get
    pushNewFrame = ProofStateT $ do
        (Env ts f a) <- get
        put (Env ts (Z.insert [] f) a)
    frameTop     = ProofStateT $ do
        (Env ts f a) <- get
        put (Env ts (Z.start f) a)
    frameBot     = ProofStateT $ do
        (Env ts f a) <- get
        put (Env ts (Z.end f) a)
    frameFwd     = ProofStateT $ do
        (Env ts f a) <- get
        put (Env ts (Z.left f) a)
    frameBwd     = ProofStateT $ do
        (Env ts f a) <- get
        put (Env ts (Z.right f) a)
    frameUpd f   = ProofStateT $ do
        (Env ts fs a) <- get
        put (Env ts (Z.replace (f (Z.cursor fs)) fs) a)
    isTopFrame = ProofStateT $ return . (\(Z.Zip ls _) -> length ls == 0) . E.getFrames =<< get
    isBotFrame = ProofStateT $ return . (\(Z.Zip _ rs) -> length rs == 1) . E.getFrames =<< get
    temp a       = push >> a >>= \r -> pop 1 >> return r

instance MonadZ3 m => MonadZ3 (ProofStateT m) where
    getSolver  = lift getSolver
    getContext = lift getContext

newtype ProofBranchT a m b = ProofBranchT { runProofBranchT :: ExceptT a m b }

instance MonadTrans (ProofBranchT a) where
    lift = ProofBranchT . lift

instance Functor m => Functor (ProofBranchT a m) where
    fmap f = ProofBranchT . (fmap f) . runProofBranchT

instance (Functor m, Monad m) => Applicative (ProofBranchT a m) where
    pure  = return
    (<*>) = ap

instance Monad m => Monad (ProofBranchT a m) where
    return  = ProofBranchT . return
    a >>= b = ProofBranchT (runProofBranchT a >>= runProofBranchT . b)

instance MonadIO m => MonadIO (ProofBranchT a m) where
    liftIO = lift . liftIO

instance (MonadZ3 m, MonadProofState m) => MonadProofState (ProofBranchT a m) where
    getInit      = lift getInit
    getInitL     = lift getInitL
    getTrans     = lift getTrans
    getTransL    = lift getTransL
    getProp      = lift getProp
    getPropL     = lift getPropL
    getFrame     = lift getFrame
    getPrevFrame = lift getPrevFrame
    getFramesUp  = lift getFramesUp
    getAbsPreds  = lift getAbsPreds
    pushNewFrame = lift pushNewFrame
    frameTop     = lift frameTop
    frameBot     = lift frameBot
    frameFwd     = lift frameFwd
    frameBwd     = lift frameBwd
    frameUpd f   = lift (frameUpd f)
    isTopFrame   = lift isTopFrame
    isBotFrame   = lift isBotFrame
    temp         = ProofBranchT . ExceptT . temp . runExceptT . runProofBranchT

instance MonadZ3 m => MonadZ3 (ProofBranchT a m) where
    getSolver  = lift getSolver
    getContext = lift getContext
