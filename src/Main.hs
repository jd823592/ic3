import IC3

import Logic
import TransitionSystem

data Result = Safe | Unsafe deriving Show

report :: [Proof] -> IO ()
report [] = error "no result"
report xs = report' Safe $ zip [1..] xs where
    report' :: Result -> [(Int, Proof)] -> IO ()
    report' r [] = putStrLn $ show r
    report' r ((n, Left  cex) : xs) = putStrLn ("cex " ++ show n ++ ": " ++ show cex) >> report' Unsafe xs
    report' r ((_, Right inv) : xs) = putStrLn ("inv: " ++ show inv)

enum :: [a] -> [a]
--enum = take 1
enum = take 10
--enum = id

main :: IO ()
main = do
    putStrLn "Please, enter i t p:"

    [i, t, p] <- fmap (map (Var BoolSort . read) . words) getLine

    ic3 (TransitionSystem i t p) >>= report . enum where
