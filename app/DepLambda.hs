{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE FlexibleContexts #-}

module DepLambda where


import Control.Monad.Except (throwError)
import Data.Functor (($>))
import Control.Monad (unless)
import Text.Megaparsec (runParser)
import qualified Parser
import Text.Pretty.Simple (pPrint)
import Control.Monad.State (MonadState, get, modify, evalState, gets)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Foldable (Foldable (foldl'), toList)
import Prelude hiding (exp)
import qualified Data.List.NonEmpty as NE
import Data.List (elemIndex)
import Control.Lens hiding (Context, from, to)

data TermUp =
    Star
    | Bound Int
    | Free Name
    | Ann TermDown TermDown
    | App TermUp TermDown
    | Pi TermDown TermDown
    deriving (Show)

data TermDown =
    Inf TermUp
    | Lambda TermDown
    deriving (Show)


data Name =
    Global Text
    | Local Int
    | Quote Int
    deriving (Eq, Show)

data Value =
    VStar
    | VNeutral Neutral
    | VPi Value (Value -> Value)
    | VFun (Value -> Value)

data Neutral =
    NFree Name
    | NApp Neutral Value

type Type = Value

type Env = [Value]

evalUp :: Env -> TermUp -> Value
evalUp _ Star = VStar
evalUp env (Bound n) = env !! n
evalUp _ (Free name) = VNeutral $ NFree name
evalUp env (Ann t _) = evalDown env t
evalUp env (App fterm arg) =
    case evalUp env fterm of
        VFun fvalue -> fvalue argEval
        VNeutral n -> VNeutral (NApp n argEval)
        _ -> error "fixme"
    where argEval = evalDown env arg
evalUp env (Pi t t') =
    VPi (evalDown env t) (\arg -> evalDown (arg:env) t') 


evalDown :: Env -> TermDown  -> Value
evalDown env (Lambda t) =
    VFun (\arg -> evalDown (arg:env) t)

evalDown env (Inf t) = evalUp env t

quote :: Value -> TermDown
quote = quote' 0

quote' :: Int -> Value -> TermDown
quote' _ VStar = Inf Star
quote' i (VNeutral n) = Inf $ quoteNeutral i n
quote' i (VFun f) =
    Lambda $ quote' (i+1) $ f (VNeutral (NFree (Quote i)))
quote' i (VPi v f) =
    Inf $ Pi (quote' i v) $ quote' (i+1) $ f (VNeutral (NFree (Quote i)))

quoteNeutral :: Int -> Neutral -> TermUp
quoteNeutral i (NFree n) = replaceQuote i n
quoteNeutral i (NApp f arg) =
    App (quoteNeutral (i+1) f) (quote' (i+1) arg)

replaceQuote :: Int -> Name -> TermUp
replaceQuote i (Quote n) = Bound (i - n - 1)
replaceQuote _ x = Free x


type TypingResult a = Either Text a
type Context = [(Name, Type)]

test :: IO ()
test = do
    pPrint $ quote (evalUp [] Star)
    pPrint $ quote (evalUp [] (Pi (Inf $ Free (Global "a")) (Inf $ Free (Global "a"))))
