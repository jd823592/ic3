module Environment where

import TransitionSystem

import Z3.Monad

type Cube = [AST]

instance Show (Z3 a) where
    show _ = "z3"

type Frame = [Cube]
type Frames = [Frame]
type Predicate = (AST, AST)
type Predicates = [Predicate]

data Env = Env { getTransitionSystem :: TransitionSystem, getFrames :: Frames, getAbsPreds :: Predicates }
