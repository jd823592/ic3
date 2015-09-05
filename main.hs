import IC3

import Logic
import Solver
import TransitionSystem

report :: Result -> IO ()
report (Left cex) = putStrLn $ show cex
report (Right inv) = putStrLn $ show inv

main :: IO ()
main = ic3 (TransitionSystem b b b) Solver >>= report where
        b :: Formula
        b = Variable 0
