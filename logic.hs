module Logic where

-- Boolean state variables
data Var = Var Int deriving (Eq, Show)

-- Literal is either positive state variable or its negation
data Lit = Pos Var | Neg Var deriving (Eq, Show)

-- Arbitrary propositional formula
data Formula = Variable Int | Negate Formula | And Formula Formula | Or Formula Formula deriving (Eq, Show)
