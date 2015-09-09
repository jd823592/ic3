import IC3

import Logic
import TransitionSystem

data Result = Safe | Unsafe deriving Show

report :: [Proof] -> IO ()
report [] = error "no result"
report xs = report' 1 Safe xs where
    report' :: Int -> Result -> [Proof] -> IO ()
    report' _ r [] = putStrLn $ show r
    report' n r (Left  cex : xs) = putStrLn ("cex " ++ show n ++ ": " ++ show cex) >> report' (n + 1) Unsafe xs
    report' n r (Right inv : xs) = putStrLn ("inv: " ++ show inv)

enum :: [a] -> [a]
--enum = take 1
enum = take 10
--enum = id

main :: IO ()
main = ic3 (TransitionSystem i t p) >>= report . enum where
        i :: Expr
        i = Var BoolSort 0

        t :: Expr
        t = Var BoolSort 0

        p :: Expr
        p = Var BoolSort 1
