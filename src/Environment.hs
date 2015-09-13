module Environment ( Cube
                   , Frame
                   , Frames
                   , Env(..)
                   ) where

import TransitionSystem

import Z3.Monad

-- Cube is a conjunction of literals
-- Frame consists of blocked cubes
type Cube = Z3 [AST]

instance Show (Z3 a) where
    show _ = "z3"

type Frame = [Cube]
type Frames = [Frame]

data Env = Env { getTransitionSystem :: TransitionSystem, getFrames :: Frames, getAbsPreds :: Z3 [(AST, AST)] }
