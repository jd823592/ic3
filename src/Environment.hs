module Environment where

import TransitionSystem

import Z3.Monad

type Cube = [AST]
type Cubes = [Cube]
type Frame = [Cube]
type Frames = [Frame]
type Predicate = (AST, AST)
type Predicates = [Predicate]

data Env = Env { getTransitionSystem :: TransitionSystem, getFrames :: Frames, getAbsPreds :: Predicates }
