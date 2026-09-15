module Main where

import Conduit
import qualified SimpleSMT as SMT
import Data.Text (unpack, Text)

average :: Monad m => ConduitT Int Void m Int
average =
    getZipSink (go <$> ZipSink sumC <*> ZipSink lengthC)
  where
    go :: Int -> Int -> Int
    go total len = total `div` fromIntegral len

countDepth :: SMT.SExpr -> Int
countDepth (SMT.Atom _) = 0
countDepth (SMT.List []) = 1
countDepth (SMT.List lst) = 1 + (maximum $ map countDepth lst)

yieldSExpr :: ConduitM Text SMT.SExpr IO ()
yieldSExpr = loop ""
  where
    loop rest = await >>= maybe (return ()) (go . (rest ++) . unpack)
    go x =
      case SMT.readSExpr x of
        Just (expr, rest) -> yield expr >> go rest
        Nothing -> loop x

maxDepth :: IO Int
maxDepth =
  runConduit
     $ stdinC
    .| decodeUtf8C
    .| yieldSExpr
    .| mapC countDepth
    .| average

main :: IO ()
main = maxDepth >>= print
