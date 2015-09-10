import IC3

import Logic
import TransitionSystem

import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import qualified ListT as L

data Result = Safe | Unsafe deriving Show

report :: L.ListT IO Proof -> IO ()
report ps = do
    L.fold report' (1, Safe) (enum ps) >>= print . snd where

    report' :: (Int, Result) -> Proof -> IO (Int, Result)
    report' (n, _) (Left  cex) = putStrLn ("cex " ++ show n ++ ": " ++ show cex) >> return (n + 1, Unsafe)
    report' (n, r) (Right inv) = putStrLn ("inv: " ++ show inv) >> return (n, r)

enum :: L.ListT IO Proof -> L.ListT IO Proof
--enum = L. take 1
--enum = L.take 10
enum = id
--enum = L.traverse (\p -> putStrLn "Press a key to get next result" >> getLine >> return p)


main :: IO ()
main = do
    putStrLn "Please, enter i t p:"

    [i, t, p] <- fmap (map (Var BoolSort . read) . words) getLine

    putStrLn ""

    report $ ic3 (TransitionSystem i t p)
