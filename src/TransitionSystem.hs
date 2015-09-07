module TransitionSystem where

import Logic

data TransitionSystem = TransitionSystem { getInit :: Expr, getTrans :: Expr, getProp :: Expr }
