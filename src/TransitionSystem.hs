module TransitionSystem where

import Logic

data TransitionSystem = TransitionSystem { getInit :: Formula, getTrans :: Formula, getProp :: Formula }
