module Proof where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Data.List
import Z3.Monad

import qualified Environment as E
import qualified Logic as L
import qualified TransitionSystem as T

class Reportable c where
    stringify :: MonadZ3 m => c -> m String

data Counterexample = Counterexample E.Cubes
data Invariant = Invariant E.Frame

instance Reportable Counterexample where
    stringify (Counterexample cs) = do
        syms  <- mapM (mapM stringifyLit) cs
        return $ "Counterexample " ++ show syms

instance Reportable Invariant where
    stringify (Invariant f) = do
        syms  <- mapM (mapM stringifyLit) f
        return $ "Invariant " ++ show syms

stringifyLit :: MonadZ3 m => AST -> m String
stringifyLit = stringifyLit' False where
    stringifyLit' :: MonadZ3 m => Bool -> AST -> m String
    stringifyLit' neg l = do
        app <- toApp l
        sym <- getSymbolString =<< getDeclName =<< getAppDecl app
        case sym of
            "not" -> stringifyLit' True =<< getAppArg app 0
            "=" -> do
                [x, y] <- mapM stringifyTerm =<< getAppArgs app
                return . concat $ [x, if neg then " /= " else " = ", y]
            "<" -> do
                [x, y] <- mapM stringifyTerm =<< getAppArgs app
                return . concat $ [x, if neg then " >= " else " < ", y]
            otherwise -> return $ (if neg then "not " else "") ++ sym

    stringifyTerm :: MonadZ3 m => AST -> m String
    stringifyTerm t = do
        k    <- getAstKind t
        app  <- toApp t
        decl <- getAppDecl app
        sym  <- getSymbolString =<< getDeclName decl
        n    <- getAppNumArgs app
        case k of
            Z3_NUMERAL_AST -> fmap show $ getInt t
            otherwise      -> do
                args <- mapM stringifyTerm =<< getAppArgs app
                if sym `elem` ["+", "-", "*", "/"]
                then return $ intercalate (" " ++ sym ++ " ") args
                else if n > 0
                then return $ sym ++  "(" ++ intercalate (", ") args ++ ")"
                else return sym

type Proof         = Either Counterexample Invariant
type ProofState    = ProofStateT Z3
type ProofBranch a = ProofBranchT a ProofState

class MonadZ3 m => MonadProofState m where
    getInit      :: m T.Formula
    getTrans     :: m T.Formula
    getProp      :: m T.Formula
    getAbsPreds  :: m E.Predicates
    getFrames    :: m E.Frames
    pushNewFrame :: m ()
    temp         :: m a -> m a

newtype ProofStateT m a = ProofStateT { runProofStateT :: StateT E.Env m a }

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
    getTrans     = ProofStateT $ fmap (T.getTrans . E.getTransitionSystem) get
    getProp      = ProofStateT $ fmap (T.getProp  . E.getTransitionSystem) get
    getFrames    = ProofStateT $ fmap E.getFrames get
    getAbsPreds  = ProofStateT $ fmap E.getAbsPreds get
    pushNewFrame = ProofStateT $ do
        (E.Env ts f a) <- get
        put (E.Env ts ([] : f) a)
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
    getTrans     = lift getTrans
    getProp      = lift getProp
    getFrames    = lift getFrames
    getAbsPreds  = lift getAbsPreds
    pushNewFrame = lift pushNewFrame
    temp         = ProofBranchT . ExceptT . temp . runExceptT . runProofBranchT

instance MonadZ3 m => MonadZ3 (ProofBranchT a m) where
    getSolver  = lift getSolver
    getContext = lift getContext

newtype MaybeDisproof a = MaybeDisproof { runDisproof :: ExceptT () (ProofBranch Counterexample) a }

instance Functor MaybeDisproof where
    fmap f = MaybeDisproof . fmap f . runDisproof

instance Applicative MaybeDisproof where
    pure  = return
    (<*>) = ap

instance Monad MaybeDisproof where
    return  = MaybeDisproof . return
    a >>= b = MaybeDisproof (runDisproof a >>= runDisproof . b)

instance MonadIO MaybeDisproof where
    liftIO = MaybeDisproof . liftIO

instance MonadProofState MaybeDisproof where
    getInit      = MaybeDisproof $ lift getInit
    getTrans     = MaybeDisproof $ lift getTrans
    getProp      = MaybeDisproof $ lift getProp
    getFrames    = MaybeDisproof $ lift getFrames
    getAbsPreds  = MaybeDisproof $ lift getAbsPreds
    pushNewFrame = MaybeDisproof $ lift pushNewFrame
    temp         = MaybeDisproof . ExceptT . temp . runExceptT . runDisproof

instance MonadZ3 MaybeDisproof where
    getSolver  = MaybeDisproof $ lift getSolver
    getContext = MaybeDisproof $ lift getContext

newtype MaybeProof a = MaybeProof { runProof :: ExceptT Invariant (ProofBranch Counterexample) a }

instance Functor MaybeProof where
    fmap f = MaybeProof . fmap f . runProof

instance Applicative MaybeProof where
    pure  = return
    (<*>) = ap

instance Monad MaybeProof where
    return  = MaybeProof . return
    a >>= b = MaybeProof (runProof a >>= runProof . b)

instance MonadIO MaybeProof where
    liftIO = MaybeProof . liftIO

instance MonadProofState MaybeProof where
    getInit      = MaybeProof $ lift getInit
    getTrans     = MaybeProof $ lift getTrans
    getProp      = MaybeProof $ lift getProp
    getFrames    = MaybeProof $ lift getFrames
    getAbsPreds  = MaybeProof $ lift getAbsPreds
    pushNewFrame = MaybeProof $ lift pushNewFrame
    temp         = MaybeProof . ExceptT . temp . runExceptT . runProof

instance MonadZ3 MaybeProof where
    getSolver  = MaybeProof $ lift getSolver
    getContext = MaybeProof $ lift getContext

run :: MonadTrans t => E.Env -> ProofBranch Counterexample Invariant -> t Z3 (Proof, E.Env)
run env = lift . (`runStateT` env) . runProofStateT . runExceptT . runProofBranchT
