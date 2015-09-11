module TransitionSystem where

import Z3.Monad

data TransitionSystem = TransitionSystem { getInit :: Z3 AST, getTrans :: Z3 AST, getProp :: Z3 AST }
