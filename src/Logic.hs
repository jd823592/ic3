module Logic ( time
             , untime
             , next
             , prev
             , getPreds
             , buildCube
             ) where

import Data.List.Split

import Z3.Monad

next :: AST -> Z3 AST
next = time 1

prev :: AST -> Z3 AST
prev = time (-1)

time :: Int -> AST -> Z3 AST
time t a = do
    k <- getAstKind a
    case k of
        Z3_APP_AST -> do
            app  <- toApp a
            decl <- getAppDecl app
            args <- getAppNumArgs app
            sort <- getSort a
            sym  <- getDeclName decl

            if args == 0
            then do
                (name, time) <- getTimedSymbol sym
                sym' <- timeSymbol (max 0 (time + t)) name
                mkVar sym' sort
            else
                mkApp decl =<< mapM (time t) =<< (getAppArgs app)
        otherwise -> return a

untime :: AST -> Z3 AST
untime a = do
    k <- getAstKind a
    case k of
        Z3_APP_AST -> do
            app  <- toApp a
            decl <- getAppDecl app
            args <- getAppNumArgs app
            sort <- getSort a
            sym  <- getDeclName decl

            if args == 0
            then do
                (name, _) <- getTimedSymbol sym
                sym' <- mkStringSymbol name
                mkVar sym' sort
            else
                mkApp decl =<< mapM untime =<< (getAppArgs app)

        otherwise -> return a

getTimedSymbol :: Symbol -> Z3 (String, Int)
getTimedSymbol s = do
    raw <- getSymbolString s

    let [sym, time] = splitOn "@" raw ++ ["0"]

    return (sym, read time)

timeSymbol :: Int -> String -> Z3 Symbol
timeSymbol t s = mkStringSymbol $ s ++ '@' : show t

getPreds :: AST -> Z3 [AST]
getPreds a = do
    k <- getAstKind a
    case k of
        Z3_APP_AST -> do
            app  <- toApp a
            decl <- getAppDecl app
            sym  <- getSymbolString =<< getDeclName decl

            if sym `elem` ["=", "<"]
            then return [a]
            else fmap concat $ mapM getPreds =<< getAppArgs app

        otherwise -> return []

buildCube :: Model -> [AST] -> Z3 [AST]
buildCube m = foldr buildCube' (return []) where
    buildCube' :: AST -> Z3 [AST] -> Z3 [AST]
    buildCube' a c = do
        ma <- modelEval m a False
        case ma of
            Nothing -> c
            Just ma' -> do
                v <- getBool ma'
                if v
                then return . (a:) =<< c
                else do
                    n <- mkNot a
                    return . (n:) =<< c
