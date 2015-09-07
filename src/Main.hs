import IC3

import Logic
import TransitionSystem

report :: Proof -> IO ()
report (Left cex) = putStrLn $ show cex
report (Right inv) = putStrLn $ show inv

main :: IO ()
main = ic3 (TransitionSystem b b b) >>= report where
        b :: Formula
        b = Variable 0
