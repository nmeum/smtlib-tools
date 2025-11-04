module Main where

import Data.Map.Strict qualified as Map
import Control.Monad (forM_)
import Control.Monad.State.Strict (State, modify, runState)
import SimpleSMT qualified as SMT
import System.IO (stdin, hGetContents)

type Stats = Map.Map String Int

mkStats :: Stats
mkStats = Map.empty

toCSV :: Stats -> String
toCSV e =
  unlines $ header : map go (Map.toList e)
  where
    seperator :: String
    seperator = ";"

    header :: String
    header = "name" ++ seperator ++ "occurrence"

    go :: (String, Int) -> String
    go (n, c) = "\"" ++ n ++ "\"" ++ seperator ++ show c

------------------------------------------------------------------------

collectName :: String -> State Stats ()
collectName name =
  modify $ Map.insertWith (+) name 1

collectBinary :: String -> SMT.SExpr -> SMT.SExpr -> State Stats ()
collectBinary name lhs rhs = do
  collectName name
  collectExpr lhs >> collectExpr rhs

collectExpr :: SMT.SExpr -> State Stats ()
collectExpr (SMT.List (SMT.Atom "=" : values))
  = forM_ values collectExpr
collectExpr (SMT.List [SMT.Atom "not", p]) = collectName "not" >> collectExpr p
collectExpr (SMT.List [SMT.Atom "bvneg", p]) = collectName "bvneg" >> collectExpr p
collectExpr (SMT.List [SMT.List [SMT.Atom "_", SMT.Atom "extract", _, _], expr])
  = collectName "expr" >> collectExpr expr
collectExpr (SMT.List [SMT.List [SMT.Atom "_", SMT.Atom "zero_extend", _], expr])
  = collectName "zero_extend" >> collectExpr expr
collectExpr (SMT.List [SMT.List [SMT.Atom "_", SMT.Atom "sign_extend", _], expr])
  = collectName "sign_extend" >> collectExpr expr
collectExpr (SMT.List [SMT.Atom "ite", cond, ifT, ifF]) = do
  collectName "ite"
  collectExpr cond >> collectExpr ifT >> collectExpr ifF
collectExpr (SMT.List [SMT.Atom "concat", lhs, rhs]) = collectBinary "concat" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvadd", lhs, rhs]) = collectBinary "bvadd" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvsub", lhs, rhs]) = collectBinary "bvsub" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvmul", lhs, rhs]) = collectBinary "bvmul" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvsdiv", lhs, rhs]) = collectBinary "bvsdiv" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvudiv", lhs, rhs]) = collectBinary "bvudiv" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvxor", lhs, rhs]) = collectBinary "bvxor" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvand", lhs, rhs]) = collectBinary "bvand" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvor", lhs, rhs]) = collectBinary "bvor" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvurem", lhs, rhs]) = collectBinary "bvurem" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvsrem", lhs, rhs]) = collectBinary "bvsrem" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvashr", lhs, rhs]) = collectBinary "bvashr" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvlshr", lhs, rhs]) = collectBinary "bvlshr" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvshl", lhs, rhs]) = collectBinary "bvshl" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvsle", lhs, rhs]) = collectBinary "bvsle" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvslt", lhs, rhs]) = collectBinary "bvslt" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvsge", lhs, rhs]) = collectBinary "bvsge" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvsgt", lhs, rhs]) = collectBinary "bvsgt" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvule", lhs, rhs]) = collectBinary "bvule" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvult", lhs, rhs]) = collectBinary "bvult" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvuge", lhs, rhs]) = collectBinary "bvuge" lhs rhs
collectExpr (SMT.List [SMT.Atom "bvugt", lhs, rhs]) = collectBinary "bvugt" lhs rhs
collectExpr (SMT.Atom _) = pure ()
collectExpr (SMT.List [SMT.Atom "_", SMT.Atom _, SMT.Atom _]) = pure ()
collectExpr e = error $ "collectExpr: Unknown expression '" ++ show e ++ "'"

collectCmd :: SMT.SExpr -> State Stats ()
collectCmd (SMT.List [SMT.Atom "check-sat-assuming", SMT.List assumptions])
  = collectName "check-sat-assuming" >> forM_ assumptions collectExpr
collectCmd (SMT.List ((SMT.Atom "set-logic") : _)) = pure ()
collectCmd (SMT.List ((SMT.Atom "declare-fun") : _)) = pure ()
collectCmd cmd = error $ "collectCmd: Unknown command '" ++ show cmd ++ "'"

collect :: [SMT.SExpr] -> State Stats ()
collect sexprs = forM_ sexprs collectCmd

------------------------------------------------------------------------

readSExprs :: String -> [SMT.SExpr]
readSExprs str = go (SMT.readSExpr str)
  where
    go :: Maybe (SMT.SExpr, String) -> [SMT.SExpr]
    go Nothing = []
    go (Just (acc, rest)) = acc : go (SMT.readSExpr rest)

getStats :: [SMT.SExpr] -> Stats
getStats exprs = snd $ collectStats exprs
  where
    collectStats e = runState (collect e) mkStats

------------------------------------------------------------------------

main :: IO ()
main = do
  exprs <- readSExprs <$> hGetContents stdin
  putStr (toCSV $! getStats exprs)
