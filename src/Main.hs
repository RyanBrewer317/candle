{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
module Main where

import qualified Data.Map as Map
import GHC.IO.Handle (hFlush)
import System.IO (stdout)
import Control.Monad (when)
import System.Environment (getArgs)
import Header (pretty, Sort(..), Pos(..))
import Typecheck (infer, normalize)
import Translate (translate)
import Parser (parseTerm, run, prettyParseError)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> do
      putStr "> "
      hFlush stdout
      src <- getLine
      when (src /= "q") $ do
        let pos = Pos "input" 1 1
        case run parseTerm Nothing pos src of
          Left err -> putStrLn err
          Right (t, _, "") -> do
            let res = translate TypeSort 0 Map.empty t
            case res of
              Left err -> putStrLn err
              Right t2 -> do
                case infer [] [] t2 of
                  Left err -> putStrLn err
                  Right t3 -> do
                    -- let bytecode = codegen [] [] t2 ++ [29, 0]
                    -- h_out <- openFile "bin.fvm" WriteMode
                    -- B.hPut h_out $ B.pack bytecode
                    -- hClose h_out
                    -- _ <- system "vendor/fvm bin.fvm"
                    putStrLn $ pretty $ normalize [] t2
                    putStrLn $ pretty t3
                    return ()
          Right (_, p, c:_) ->
            putStrLn $
              prettyParseError p Nothing $ "unexpected `" ++ c:"`"
        main
    filename:_ -> do
      let pos = Pos filename 1 1
      src <- readFile filename
      case run parseTerm Nothing pos src of
        Left err -> putStrLn err
        Right (t, _, "") -> do
          let res = translate TypeSort 0 Map.empty t
          case res of
            Left err ->
              putStrLn err
            Right t2 -> do
              case infer [] [] t2 of
                Left err -> putStrLn err
                Right t3 -> do
                  -- let bytecode = codegen [] [] t2 ++ [29, 0]
                  -- h_out <- openFile "bin.fvm" WriteMode
                  -- B.hPut h_out $ B.pack bytecode
                  -- hClose h_out
                  -- putStrLn "success!"
                  -- _ <- system "vendor/fvm bin.fvm"
                  -- putStrLn $ pretty $ normalize [] t2
                  putStrLn $ pretty t3
                  return ()
        Right (_, p, c:_) ->
          putStrLn $
            prettyParseError p Nothing $ "unexpected `" ++ c:"`"
