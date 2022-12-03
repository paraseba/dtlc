module Main where

import qualified Repl

main :: IO ()
main = do
    Repl.ioRepl
