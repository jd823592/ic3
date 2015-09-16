import IC3
import Logic
import TransitionSystem
import Proof

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import qualified Data.Traversable as T
import qualified ListT as L

import Z3.Monad

data Report = Safe | Unsafe deriving Show

report :: L.ListT Z3 Proof -> IO ()
report ps = evalZ3 (L.fold report' (1, Safe) (enum ps)) >>= print . snd where
    report' :: (Int, Report) -> Proof -> Z3 (Int, Report)
    report' (n, _) (Left  cex) = liftIO (putStrLn $ "cex " ++ show n ++ ": " ++ show cex) >> return (n + 1, Unsafe)
    report' (n, r) (Right inv) = liftIO (putStrLn $ "inv: " ++ show inv) >> return (n, r)

enum :: L.ListT Z3 Proof -> L.ListT Z3 Proof
--enum = L. take 1
--enum = L.take 10
enum = id
--enum = L.traverse (\p -> liftIO (putStrLn "Press a key to get next result" >> getLine) >> return p)

input :: Z3 TransitionSystem
input = do
    pc  <- mkIntVar =<< mkStringSymbol "pc"
    pc' <- next pc
    x   <- mkIntVar =<< mkStringSymbol "x"
    x'  <- next x
    c0  <- mkInt 0 =<< mkIntSort
    c1  <- mkInt 1 =<< mkIntSort
    c2  <- mkInt 2 =<< mkIntSort


    -- (pc = 0)
    --
    -- (pc = 0) and (next(pc) = 1) and (next(x) = 0)
    -- (pc = 1) and (x >= 0) and (next(pc) = 1) and (next(x) = x + 1)
    -- (pc = 1) and (x < 0) and (next(pc) = 2) and (next(x) = x)
    --
    -- (pc != 2)


    i <- mkEq pc c0
    t <- mkOr =<< T.sequence
        [ mkAnd =<< T.sequence [mkEq pc c0, mkEq pc' c1, mkEq x' c0]
        , mkAnd =<< T.sequence [mkEq pc c1, mkEq pc' c1, mkNot =<< mkLt x c0, mkEq x' =<< mkAdd [x, c1]]
        , mkAnd =<< T.sequence [mkEq pc c1, mkEq pc' c2,           mkLt x c0, mkEq x' x]
        ]
    p <- mkNot =<< mkEq pc c2

    return (TransitionSystem i t p)

main :: IO ()
main = report $ ic3 =<< lift input
