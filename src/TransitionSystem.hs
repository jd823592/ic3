module TransitionSystem where

import Z3.Monad

type Formula = AST

data TransitionSystem = TransitionSystem { getInit :: Formula, getTrans :: Formula, getProp :: Formula }
