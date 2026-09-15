module Main where

import Conduit
import Data.Functor (($>))
import Data.List (uncons)
import Data.Text (Text, unpack)
import SimpleSMT qualified as SMT
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

z3Solver :: IO SMT.Solver
z3Solver = do
  -- l <- SMT.newLogger 0
  s <- SMT.newSolver "z3" ["-smt2", "-in"] Nothing
  return s

simplify :: SMT.Solver -> SMT.SExpr -> IO SMT.SExpr
simplify s e = SMT.command s $ SMT.List [SMT.Atom "simplify", e]

------------------------------------------------------------------------

fwdCmd :: SMT.Solver -> SMT.SExpr -> IO SMT.SExpr
fwdCmd solver expr = SMT.command solver expr $> expr

transSExpr :: String -> SMT.Solver -> SMT.SExpr -> IO SMT.SExpr
transSExpr _ s e@(SMT.List ((SMT.Atom "set-logic") : _)) = fwdCmd s e
transSExpr _ s e@(SMT.List ((SMT.Atom "declare-fun") : _)) = fwdCmd s e
transSExpr a s e@(SMT.List xs) =
  let recur = SMT.List <$> mapM (transSExpr a s) xs
   in case uncons xs of
        Just (SMT.Atom name, _) ->
          if name == a
            then simplify s e
            else recur
        _ -> recur
transSExpr _ _ e = pure e

yieldSExpr :: ConduitM Text SMT.SExpr IO ()
yieldSExpr = loop ""
  where
    loop rest = await >>= maybe (return ()) (go . (rest ++) . unpack)
    go x =
      case SMT.readSExpr x of
        Just (expr, rest) -> yield expr >> go rest
        Nothing -> loop x

------------------------------------------------------------------------

transformStdin :: String -> SMT.Solver -> IO ()
transformStdin atomName solver =
  runConduit $
    stdinC
      .| decodeUtf8C
      .| yieldSExpr
      .| mapMC (transSExpr atomName solver)
      .| mapM_C printSExpr
  where
    printSExpr :: SMT.SExpr -> IO ()
    printSExpr e = putStrLn $ SMT.showsSExpr e ""

main :: IO ()
main = do
  args <- getArgs
  case args of
    [exprName] -> z3Solver >>= transformStdin exprName
    _ -> do
      hPutStrLn stderr "Expected single name of expression to simplify"
      exitFailure
