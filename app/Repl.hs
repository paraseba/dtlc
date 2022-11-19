{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}

module Repl where

import Control.Monad.State (MonadState, StateT, liftIO, evalStateT)
import Lambda
import Text.Megaparsec (ParseErrorBundle, runParser)
import Data.Text (Text)
import Data.Void (Void)
import qualified Parser
import qualified Streamly.Prelude as Stream
import qualified Data.List.NonEmpty as NE
import qualified Streamly.Console.Stdio as Stdio
import qualified Streamly.Data.Fold as Fold
import qualified Data.Text as Text
import Data.Function ((&))
import qualified Data.Text.IO as TIO
import qualified Streamly.Unicode.Stream as UniStream
import Data.Foldable (fold)
import Data.Coerce (coerce)

repl :: MonadState Context m => (EvalResult -> m ()) -> (ParseErrorBundle Text Void -> m ()) -> Text -> m ()
repl showResult showParseError statement =  do
    case runParser Parser.statementParser "input" statement of
        Left err -> showParseError err
        Right parsed -> do
            res <- evaluateSt parsed
            showResult res

emptyContext :: Context
emptyContext = []

printingRepl :: Stream.SerialT (StateT Context IO) Text -> IO ()
printingRepl stream = 
    stream
        & Stream.mapM (repl (liftIO . printEvalRes) (liftIO . print))
        & Stream.drain
        & flip evalStateT emptyContext

basicRepl :: NE.NonEmpty Text -> IO ()
basicRepl inputs =
    inputs
        & Stream.fromFoldable
        & printingRepl 

ioRepl :: IO ()
ioRepl =
    Stream.unfold Stdio.read ()
        & UniStream.decodeUtf8
        & Stream.splitOnSuffix (== '\n') (Fold.foldl' Text.snoc "")
        & printingRepl

printEvalRes :: EvalResult -> IO ()
printEvalRes (EvAssumed ids) = TIO.putStrLn $ "Assumed: " <> names
    where names = fold $ NE.intersperse ", " (identifier2text <$> ids)
printEvalRes (EvError err) = putStrLn $ "Error: " <> show err
printEvalRes (EvRes val typ) =
    TIO.putStrLn $ display (quote val) <> " :: " <> displayType typ


identifier2text :: Parser.Identifier -> Text
identifier2text = coerce



test :: IO ()
test = do
    basicRepl
        [ "assume (alpha :: *) (beta :: *)"
        , "assume (a :: alpha) (b :: beta)"
        , "((λx -> x) :: alpha -> alpha) a"
        ]

    putStrLn "///////////////////////////"


    basicRepl
        [ "assume (α :: *) (y :: α)"
        , "((λx → x) :: α → α) y"
        , "assume (β :: *) "
        , "((λx y → x) :: (β → β) → α → β → β) (λx → x) y"
        ]

    putStrLn "///////////////////////////"
    basicRepl
        [ "assume (α :: *) (y :: α)"
        , "((λx → x) :: α → α) y"
        , "assume (β :: *) "
        , "((λx y → x) :: (β → β) → α → β → β) "
        ]

    putStrLn "///////////////////////////"
    basicRepl
        [ "assume (β :: *) (f :: β -> β) (b :: β)"
        , "((\\x -> x ) :: β -> β) (f b)"
        ]
