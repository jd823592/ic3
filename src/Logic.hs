module Logic ( time
             , untime
             , next
             , prev
             , getStatePreds
             , buildCube
             , expandCube
             ) where

import Control.Monad
import Data.List
import Data.List.Split
import qualified Data.Map as Map
import Debug.Trace

import Z3.Monad

next :: MonadZ3 z3 => AST -> z3 AST
next = time 1

prev :: MonadZ3 z3 => AST -> z3 AST
prev = time (-1)

time :: MonadZ3 z3 => Int -> AST -> z3 AST
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

untime :: MonadZ3 z3 => AST -> z3 AST
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

getTimedSymbol :: MonadZ3 z3 => Symbol -> z3 (String, Int)
getTimedSymbol s = do
    raw <- getSymbolString s

    let (sym : time : _) = splitOn "@" raw ++ ["0"]

    return (sym, read time)

timeSymbol :: MonadZ3 z3 => Int -> String -> z3 Symbol
timeSymbol t s = mkStringSymbol $ s ++ '@' : show t

getStatePreds :: MonadZ3 z3 => AST -> z3 [AST]
getStatePreds = getStatePreds' [] where
    getStatePreds' :: MonadZ3 z3 => [AST] -> AST -> z3 [AST]
    getStatePreds' preds a = do
        k <- getAstKind a
        case k of
            Z3_APP_AST -> do
                app  <- toApp a
                decl <- getAppDecl app
                sym  <- getSymbolString =<< getDeclName decl

                if sym `elem` ["=", "<"]
                then do
                    vars  <- getVars a
                    syms  <- mapM (getDeclName <=< getAppDecl <=< toApp) vars
                    times <- fmap (length . nub . map snd) $ mapM getTimedSymbol syms

                    if times == 1
                    then return . (: preds) =<< untime a
                    else return preds
                else foldM getStatePreds' preds =<< getAppArgs app
            otherwise -> return []

getVars :: MonadZ3 z3 => AST -> z3 [AST]
getVars = getVars' [] where
    getVars' :: MonadZ3 z3 => [AST] -> AST -> z3 [AST]
    getVars' vars a = do
        k <- getAstKind a
        case k of
            Z3_APP_AST -> do
                app  <- toApp a
                decl <- getAppDecl app
                args <- getAppNumArgs app

                if args == 0
                then return (a : vars)
                else foldM getVars' vars =<< (getAppArgs app)
            otherwise -> return vars

buildCube :: MonadZ3 z3 => Model -> [AST] -> z3 [AST]
buildCube m = foldr buildCube' (return []) where
    buildCube' :: MonadZ3 z3 => AST -> z3 [AST] -> z3 [AST]
    buildCube' a c = do
        ma <- modelEval m a False
        case ma of
            Nothing -> c
            Just ma' -> do
                v <- getBoolValue ma'
                case v of
                    Just True  -> return . (a:) =<< c
                    Just False -> liftM2 (:) (mkNot a) c
                    Nothing    -> c

expandCube :: MonadZ3 z3 => [(AST, AST)] -> [AST] -> z3 [AST]
expandCube exp = mapM (expandLit exp)

expandLit ::  MonadZ3 z3 => [(AST, AST)] -> AST -> z3 AST
expandLit exp l = expandLit' False l where
    expandLit' :: MonadZ3 z3 => Bool -> AST -> z3 AST
    expandLit' neg l = do
        app  <- toApp l
        decl <- getAppDecl app
        sym <- getSymbolString =<< getDeclName decl
        if sym == "not"
        then expandLit' True =<< getAppArg app 0
        else (if neg then mkNot else return) =<< expandAtom l

    expandAtom :: MonadZ3 z3 => AST -> z3 AST
    expandAtom = return . (Map.fromList exp Map.!)
