{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Proof where

import Control.Applicative
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State

import qualified Control.Monad.State.Class as S

import Environment

import Z3.Monad

data Counterexample = Counterexample [Cube] deriving Show
data Invariant = Invariant Frame deriving Show

type Proof = Either Counterexample Invariant

class MonadZ3 m => MonadIC3 m where
    pushNewFrame :: m ()

    temp :: m a -> m a
    temp a = lift $ push >> a >>= \r -> pop 1 >> return r

newtype MonadZ3 z3 => ProofStateT z3 a = ProofStateT { runProofStateT :: StateT Env z3 a }
    deriving (Functor, Applicative, Monad, MonadIO, S.MonadState Env)

newtype MonadZ3 z3 => ProofBranchT a z3 b = ProofBranchT { runProofBranchT :: ExceptT a (ProofStateT z3) b }
    deriving (Functor, Applicative, Monad, MonadIO, S.MonadState Env, MonadError a)

type ProofState    = ProofStateT Z3
type ProofBranch e = ProofBranchT e Z3
type MaybeDisproof = ExceptT () (ProofBranch Counterexample)
type MaybeProof    = ExceptT Invariant (ProofBranch Counterexample)

instance MonadTrans ProofStateT where
    lift = ProofStateT . lift

instance MonadTrans (ProofBranchT a) where
    lift = ProofBranchT . lift

instance MonadZ3 z3 => MonadZ3 (ProofStateT z3) where
    getSolver  = lift getSolver
    getContext = lift getContext

instance MonadZ3 z3 => MonadZ3 (ProofBranchT a z3) where
    getSolver  = lift getSolver
    getContext = lift getContext

instance MonadZ3 z3 => MonadIC3 (ProofStateT z3) where
    pushNewFrame = do
        env <- ProofStateT get
        ProofStateT . put $ Env (getTransitionSystem env) ([] : getFrames env) (getAbsPreds env)

instance MonadZ3 z3 => MonadIC3 (ProofBranchT a z3) where
    pushNewFrame = lift . pushNewFrame
