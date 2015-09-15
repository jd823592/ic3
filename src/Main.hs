import IC3
import Logic
import TransitionSystem
import Proof

import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import qualified Data.Traversable as T
import qualified ListT as L

import Z3.Monad

data Report = Safe | Unsafe deriving Show

report :: L.ListT IO Proof -> IO ()
report ps = do
    L.fold report' (1, Safe) (enum ps) >>= print . snd where

    report' :: (Int, Report) -> Proof -> IO (Int, Report)
    report' (n, _) (Left  cex) = putStrLn ("cex " ++ show n ++ ": " ++ show cex) >> return (n + 1, Unsafe)
    report' (n, r) (Right inv) = putStrLn ("inv: " ++ show inv) >> return (n, r)

enum :: L.ListT IO Proof -> L.ListT IO Proof
--enum = L. take 1
--enum = L.take 10
enum = id
--enum = L.traverse (\p -> putStrLn "Press a key to get next result" >> getLine >> return p)

main :: IO ()
main = do
    let pcM = mkIntVar =<< mkStringSymbol "pc"
    let xM  = mkIntVar =<< mkStringSymbol "x"
    let c0M = mkInt 0 =<< mkIntSort
    let c1M = mkInt 1 =<< mkIntSort
    let c2M = mkInt 2 =<< mkIntSort

    let i = do
                pc <- pcM
                c0 <- c0M
                mkEq pc c0
    -- (pc = 0) and (next(pc) = 1) and (next(x) = 0)
    -- (pc = 1) and (x >= 0) and (next(pc) = 1) and (next(x) = x + 1)
    -- (pc = 1) and (x < 0) and (next(pc) = 2) and (next(x) = x)
    let t = do
                pc  <- pcM
                pc' <- next =<< pcM
                x   <- xM
                x'  <- next =<< xM
                c0  <- c0M
                c1  <- c1M
                c2  <- c2M

                mkOr =<< T.sequence
                    [ mkAnd =<< T.sequence [mkEq pc c0, mkEq pc' c1, mkEq x' c0]
                    , mkAnd =<< T.sequence [mkEq pc c1, mkEq pc' c1, mkNot =<< mkLt x c0, mkEq x' =<< mkAdd [x, c1]]
                    , mkAnd =<< T.sequence [mkEq pc c1, mkEq pc' c2,           mkLt x c0, mkEq x' x]
                    ]
    let p = do
                pc <- pcM
                c2 <- c2M
                mkNot =<< mkEq pc c2

    report $ ic3 (TransitionSystem i t p)
