module Logic (Sort(..), Expr(..), toZ3) where

import qualified Data.Traversable as T

import qualified Z3.Monad as Z3

data Sort = BoolSort
          | IntSort
          | BVSort Int
          | ArrSort Sort
          deriving (Eq, Show)

data Expr = Var Sort Int
          | Const Sort Int
          | Lt  Expr Expr
          | Eq  Expr Expr
          | Neg Expr
          | And [Expr]
          | Or  [Expr]
          | Add [Expr]
          | Sub [Expr]
          | Mul [Expr]
          | Div Expr Expr
          | Rem Expr Expr
          | Sel Expr Expr
          | Upd Expr Expr Expr
          | Exists Expr Expr
          | Forall Expr Expr
          deriving (Eq, Show)

toZ3 :: Z3.MonadZ3 z3 => Expr -> z3 Z3.AST
toZ3 (Var BoolSort i)     = Z3.mkBoolVar =<< Z3.mkStringSymbol ("b" ++ show i)
toZ3 (Var IntSort i)      = Z3.mkIntVar =<< Z3.mkStringSymbol ("i" ++ show i)
toZ3 (Var (BVSort w) i)   = do
                                s <- Z3.mkStringSymbol ("i" ++ show i)
                                Z3.mkBvVar s w
toZ3 (Const BoolSort 0)   = Z3.mkBool False
toZ3 (Const BoolSort _)   = Z3.mkBool True
toZ3 (Const IntSort v)    = Z3.mkIntNum v
toZ3 (Const (BVSort w) v) = Z3.mkBvNum w v
toZ3 (Lt a b)             = do
                                a' <- toZ3 a
                                b' <- toZ3 b
                                Z3.mkLt a' b'
toZ3 (Eq a b)             = do
                                a' <- toZ3 a
                                b' <- toZ3 b
                                Z3.mkEq a' b'
toZ3 (Neg e)              = Z3.mkNot =<< toZ3 e
toZ3 (And e)              = Z3.mkAnd =<< T.sequence (map toZ3 e)
toZ3 (Or e)               = Z3.mkOr =<< T.sequence (map toZ3 e)
toZ3 (Add e)              = Z3.mkAdd =<< T.sequence (map toZ3 e)
toZ3 (Sub e)              = Z3.mkSub =<< T.sequence (map toZ3 e)
toZ3 (Mul e)              = Z3.mkMul =<< T.sequence (map toZ3 e)
toZ3 (Div a b)            = do
                                a' <- toZ3 a
                                b' <- toZ3 b
                                Z3.mkDiv a' b'
toZ3 (Rem a b)            = do
                                a' <- toZ3 a
                                b' <- toZ3 b
                                Z3.mkRem a' b'
toZ3 (Sel a b)            = do
                                a' <- toZ3 a
                                b' <- toZ3 b
                                Z3.mkSelect a' b'
toZ3 (Upd a b c)          = do
                                a' <- toZ3 a
                                b' <- toZ3 b
                                c' <- toZ3 c
                                Z3.mkStore a' b' c'
--toZ3 (Exists a b ) =
--toZ3 (Forall a b ) =
