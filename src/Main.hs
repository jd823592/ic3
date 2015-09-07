import IC3

import Logic
import TransitionSystem

report :: Proof -> IO ()
report (Left cex) = putStrLn $ show cex
report (Right inv) = putStrLn $ show inv

main :: IO ()
main = ic3 (TransitionSystem i t p) >>= report where
        i :: Expr
        i = Var BoolSort 0

        t :: Expr
        t = Var BoolSort 0

        p :: Expr
        p = Var BoolSort 0
