module Main where

import Data.Maybe (isNothing)
import Control.Monad.IO.Class (liftIO)
import Control.Monad (forM_, void, when, unless)
import Control.Monad.State.Strict (StateT, gets, modify, runStateT)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import SimpleSMT qualified as SMT
import System.IO (stdin, hGetContents)
import Options.Applicative qualified as OPT

data Opts = Opts
  { optElimAnds :: Bool,
    optLogic :: Maybe String,
    optTrackAssert :: Bool }

optsParser :: OPT.Parser Opts
optsParser =
  Opts
    <$> OPT.switch
      ( OPT.long "eliminate-ands"
          <> OPT.short 'e'
          <> OPT.help "Eliminate outer and expressions in check-sat-assuming"
      )
    <*> OPT.optional
      ( OPT.strOption $
          OPT.long "logic"
            <> OPT.short 'l'
            <> OPT.metavar "LOGIC"
            <> OPT.help "Overwrite logic"
      )
    <*> OPT.switch
      ( OPT.long "track-assertions"
          <> OPT.short 'a'
          <> OPT.help "Track push/pop assertion stacks"
      )

------------------------------------------------------------------------

data UnwindEnv
  = UnwindEnv
  { trackAsserts :: Bool,
    elimAnds :: Bool,
    setLogic :: Maybe String,
    logicWritten :: Bool,
    declaredVars :: Map.Map String SMT.SExpr,
    assertStack :: [[SMT.SExpr]],
    exprs :: [SMT.SExpr]
  }
  deriving (Show, Eq)

mkUnwindEnv :: Bool -> Bool -> Maybe String -> UnwindEnv
mkUnwindEnv trackAsserts andElim setLogic =
  UnwindEnv trackAsserts andElim setLogic False Map.empty [] []

------------------------------------------------------------------------

buildMap :: [SMT.SExpr] -> Map.Map String SMT.SExpr
buildMap exprs =
  Map.fromList $
    foldl (\acc x -> toVarPair x : acc) [] exprs

toVarPair :: SMT.SExpr -> (String, SMT.SExpr)
toVarPair (SMT.List [SMT.Atom varName, varValue]) = (varName, varValue)
toVarPair _ = error "invalid let binding"

substVars :: Map.Map String SMT.SExpr -> SMT.SExpr -> SMT.SExpr
substVars varMap atom@(SMT.Atom name) =
  fromMaybe atom $ Map.lookup name varMap
substVars varMap (SMT.List lst) =
  SMT.List $ map (substVars varMap) lst

inlineLet' :: Map.Map String SMT.SExpr -> SMT.SExpr -> SMT.SExpr
inlineLet' varMap (SMT.List [SMT.Atom "let", SMT.List letBind, letBody]) =
  let varMap' = Map.union (buildMap letBind) varMap
    in substVars varMap' (inlineLet' varMap' letBody)
  where
inlineLet' varMap atom = substVars varMap atom

inlineLet :: SMT.SExpr -> SMT.SExpr
inlineLet = inlineLet' Map.empty

------------------------------------------------------------------------

newAssertLevel :: StateT UnwindEnv IO ()
newAssertLevel =
  modify (\s -> s {assertStack = [] : assertStack s})

popAssertLevel :: StateT UnwindEnv IO ()
popAssertLevel = modify go
  where
    go s@UnwindEnv {assertStack = []} = s
    go s@UnwindEnv {assertStack = _ : xs} = s {assertStack = xs}

addAssertion :: SMT.SExpr -> StateT UnwindEnv IO ()
addAssertion assertions' = do
  stk <- gets assertStack
  let newStk = case stk of
        (x : xs) -> (x ++ assertions) : xs
        [] -> [assertions]
  modify (\s -> s {assertStack = newStk})
  where
    assertions = [inlineLet assertions']

addExpr :: SMT.SExpr -> StateT UnwindEnv IO ()
addExpr expr =
  modify (\s -> s {exprs = exprs s ++ [expr]})

-- | Retrieve a list of conjunction from and expressions for check-sat-assuming.
subsumeAnds :: SMT.SExpr -> [SMT.SExpr]
subsumeAnds (SMT.List [SMT.Atom "and", lhs@(SMT.List (SMT.Atom "and" : _)), rhs])
  = subsumeAnds lhs ++ subsumeAnds rhs
subsumeAnds (SMT.List [SMT.Atom "and", lhs, rhs@(SMT.List (SMT.Atom "and" : _))])
  = subsumeAnds lhs ++ subsumeAnds rhs
subsumeAnds (SMT.List [SMT.Atom "and", lhs, rhs])
  = subsumeAnds lhs ++ subsumeAnds rhs
subsumeAnds expr = [expr] -- Stop recursion on first non-and expression.

getAsserts :: StateT UnwindEnv IO [SMT.SExpr]
getAsserts = do
  andOpt <- gets elimAnds
  consLs <- gets (concat . reverse . assertStack)
  if andOpt
    then pure [SMT.List (inlineAnds consLs)]
    else pure [SMT.List consLs]
  where
    inlineAnds :: [SMT.SExpr] -> [SMT.SExpr]
    inlineAnds = concat . map subsumeAnds

completeQuery :: StateT UnwindEnv IO ()
completeQuery = do
  query <- gets exprs
  liftIO $ putStr (serialize query)

  track <- gets trackAsserts
  if track
    then modify ( \s -> s { exprs = [] })
    else modify ( \s -> s { exprs = [], assertStack = [] })
  where
    serialize :: [SMT.SExpr] -> String
    serialize = unlines . map (`SMT.showsSExpr` "")

addVariable :: String -> SMT.SExpr -> StateT UnwindEnv IO ()
addVariable name expr = do
  vars <- gets declaredVars
  when (isNothing $ Map.lookup name vars) $ do
    liftIO $ putStrLn (SMT.showsSExpr expr "")
    modify (\s -> s {declaredVars = Map.insert name expr vars})

transExpr :: SMT.SExpr -> StateT UnwindEnv IO ()
transExpr (SMT.List [SMT.Atom "push", SMT.Atom arg]) = do
  let num = (read arg :: Integer)
  forM_ [1 .. num] (const newAssertLevel)
transExpr (SMT.List [SMT.Atom "pop", SMT.Atom arg]) = do
  let num = (read arg :: Integer)
  forM_ [1 .. num] (const popAssertLevel)
transExpr (SMT.List [SMT.Atom "assert", xs]) =
  addAssertion xs
transExpr (SMT.List [SMT.Atom "check-sat"]) = do
  asserts <- getAsserts
  addExpr $ SMT.List (SMT.Atom "check-sat-assuming" : asserts)
  completeQuery
transExpr expr@(SMT.List ((SMT.Atom "set-logic") : _)) = do
  wasWritten <- gets logicWritten
  unless (wasWritten) $ do
    mayLogic <- gets setLogic
    case mayLogic of
      Just l ->
        liftIO $ putStrLn ((SMT.showsSExpr $ SMT.List [SMT.Atom "set-logic", SMT.Atom l]) "")
      Nothing ->
        liftIO $ putStrLn ((SMT.showsSExpr expr) "")
    modify (\s -> s {logicWritten = True})
transExpr expr@(SMT.List ((SMT.Atom "declare-fun") : (SMT.Atom name) : _)) = addVariable name expr
transExpr (SMT.List ((SMT.Atom "set-option" : _))) = pure ()
transExpr (SMT.List ((SMT.Atom "set-info") : _)) = pure ()
transExpr (SMT.List ((SMT.Atom "get-value") : _)) = pure ()
transExpr (SMT.List ((SMT.Atom "exit") : _)) = modify (\s -> s { assertStack = [] })
transExpr expr = addExpr expr

transform :: [SMT.SExpr] -> StateT UnwindEnv IO ()
transform sexprs = forM_ sexprs transExpr

------------------------------------------------------------------------

readSExprs :: String -> [SMT.SExpr]
readSExprs str = go (SMT.readSExpr str)
  where
    go :: Maybe (SMT.SExpr, String) -> [SMT.SExpr]
    go Nothing = []
    go (Just (acc, rest)) = acc : go (SMT.readSExpr rest)

getQueries :: Opts -> [SMT.SExpr] -> IO ()
getQueries opts exprs = void $ runTransform exprs
  where
    runTransform e =
      runStateT
        (transform e)
        $ mkUnwindEnv (optTrackAssert opts) (optElimAnds opts) (optLogic opts)

main :: IO ()
main = do
  args  <- OPT.execParser cmd
  exprs <- readSExprs <$> hGetContents stdin

  getQueries args exprs
  where
    cmd :: OPT.ParserInfo Opts
    cmd =
      OPT.info
        (optsParser OPT.<**> OPT.helper)
        ( OPT.fullDesc
            <> OPT.progDesc "normalize smt-lib inputs"
        )
