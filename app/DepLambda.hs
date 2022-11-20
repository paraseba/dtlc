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
import Debug.Trace

data TermUp =
    Star
    | Bound Int
    | Free Name
    | Ann TermDown TermDown
    | App TermUp TermDown
    | Pi TermDown TermDown
    | Nat
    | Zero
    | Succ TermDown
    | NatElim TermDown TermDown TermDown TermDown
    deriving (Show, Eq)

data TermDown =
    Inf TermUp
    | Lambda TermDown
    deriving (Show, Eq)


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
    | VNat
    | VZero
    | VSucc Value

data Neutral =
    NFree Name
    | NApp Neutral Value
    | NNatElim  Value Value Value Neutral

type Type = Value

type Env = [Value]

vapp :: Value -> Value -> Value
vapp (VFun f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalUp :: Env -> TermUp -> Value
evalUp _ Star = VStar
evalUp env (Bound n) = env !! n
evalUp _ (Free name) = VNeutral $ NFree name
evalUp env (Ann t _) = evalDown env t
evalUp env (App fterm arg) =
    case evalUp env fterm of
        VFun fvalue -> fvalue argEval
        n@(VNeutral _) -> vapp n argEval
        _ -> error "fixme"
    where argEval = evalDown env arg
evalUp env (Pi t t') =
    VPi (evalDown env t) (\arg -> evalDown (arg:env) t')
evalUp _ Nat = VNat
evalUp _ Zero = VZero
evalUp env (Succ n) = VSucc (evalDown env n)
evalUp env (NatElim m mz ms k) =
    case kVal of
       VZero -> mzVal
       VSucc l -> let rec = evalUp env (NatElim m mz ms (quote l))
                  in msVal `vapp` l `vapp` rec
       VNeutral k' -> VNeutral $ NNatElim mVal mzVal msVal k'

       _ -> error "Internal error, natElim'ing not a number"
    where
        mzVal = evalDown env mz
        msVal = evalDown env ms
        kVal = evalDown env k
        mVal = evalDown env m


evalDown :: Env -> TermDown  -> Value
evalDown env (Lambda t) =
    VFun (\arg -> evalDown (arg:env) t)

evalDown env (Inf t) = evalUp env t

emptyEnv :: Env
emptyEnv = []

quote :: Value -> TermDown
quote = quote' 0

quote' :: Int -> Value -> TermDown
quote' _ VStar = Inf Star
quote' i (VNeutral n) = Inf $ quoteNeutral i n
quote' i (VFun f) =
    Lambda $ quote' (i+1) $ f (VNeutral (NFree (Quote i)))
quote' i (VPi v f) =
    Inf $ Pi (quote' i v) $ quote' (i+1) $ f (VNeutral (NFree (Quote i)))
quote' _ VNat = Inf Nat
quote' _ VZero = Inf Zero
quote' i (VSucc n) = Inf (Succ $ quote' i n)

quoteNeutral :: Int -> Neutral -> TermUp
quoteNeutral i (NFree n) = replaceQuote i n
quoteNeutral i (NApp f arg) =
    App (quoteNeutral (i+1) f) (quote' (i+1) arg)

quoteNeutral i (NNatElim t1 t2 t3 n) =
    NatElim (quote' i t1)
            (quote' i t2)
            (quote' i t3)
            (Inf (quoteNeutral i n))

replaceQuote :: Int -> Name -> TermUp
replaceQuote i (Quote n) = Bound (i - n - 1)
replaceQuote _ x = Free x


type TypingResult a = Either Text a
type Context = [(Name, Type)]


typeUp :: Context -> TermUp -> TypingResult Type
typeUp = typeUp' 0

typeUp' :: Int -> Context -> TermUp -> TypingResult Type
typeUp' _ _ (Bound _) = throwError "This should never be called"

typeUp' _ ctx (Free name) =
    case lookup name ctx of
        Just typ  -> pure typ
        _ -> throwError $ "Name not found " <> Text.pack (show name)

typeUp' i ctx (Ann e rho) = do
    typeDown' i ctx rho VStar
    let tau = evalDown emptyEnv rho
    typeDown' i ctx e tau
    pure tau

typeUp' _ _ Star = pure VStar

typeUp' i ctx (App e e') = do
    ftype <- typeUp' i ctx e
    case ftype of
        VPi tau tau' -> do
            typeDown' i ctx e' tau
            pure $ tau' (evalDown emptyEnv e')
        _ -> throwError "Invalid application"

typeUp' i ctx (Pi rho rho') = do
-- (Pi (Inf Star) (Inf $ Bound 0))
    typeDown' i ctx rho VStar
    let tau = evalDown emptyEnv rho
    typeDown' (i + 1) ((Local i, tau):ctx) (substDown 0 (Free (Local i)) rho') VStar
    pure VStar

typeUp' _ _ Nat = pure VStar
typeUp' _ _ Zero = pure VNat
typeUp' i ctx (Succ n) = typeDown' i ctx n VNat $> VNat
typeUp' i ctx (NatElim m mz ms k) = do
    typeDown' i ctx m (VPi VNat (const VStar))
    let tau = mVal `vapp` VZero
    typeDown' i ctx mz tau
    typeDown' i ctx k VNat
    typeDown' i ctx ms (VPi VNat (\l -> VPi (mVal `vapp` l) (\_ -> mVal `vapp` VSucc l)))
    pure (mVal `vapp` kVal)
    where
        mVal = evalDown [] m
        kVal = evalDown [] k



typeDown' :: Int -> Context -> TermDown -> Type -> TypingResult ()
typeDown' i ctx (Lambda e) (VPi tau tau')  =
    typeDown' (i + 1)
              ((Local i, tau) : ctx)
              (substDown 0 (Free (Local i)) e)
              (tau' (VNeutral (NFree (Local i))))

typeDown' _ _ (Lambda _) x  = throwError $ "Cannot type lambda: " <> Text.pack (show (quote x))

typeDown' i ctx (Inf e) v = do
    actual <- typeUp' i ctx e
    unless (quote actual == quote v) $
        throwError "Type mismatch"

substDown :: Int -> TermUp -> TermDown -> TermDown
substDown i replacement (Lambda t) =
    Lambda (substDown (i + 1) replacement t)

substDown i replacement (Inf t) =
    Inf (substUp i replacement t)

substUp :: Int -> TermUp -> TermUp -> TermUp
substUp _ _ Star = Star

substUp i replacement (Bound n)
    | i == n = replacement
    | otherwise = Bound n

substUp _ _ (Free name) = Free name

substUp i replacement (Ann e tau) =
    Ann (substDown i replacement e) (substDown i replacement tau)

substUp i replacement (App fterm argterm) =
    App (substUp i replacement fterm)
        (substDown i replacement argterm)

substUp i replacement (Pi tau tau') =
    Pi (substDown i replacement tau) (substDown (i + 1) replacement tau')

substUp _ _ Nat = Nat
substUp _ _ Zero = Zero
substUp i r (Succ n) = Succ $ substDown i r n
substUp i r (NatElim t1 t2 t3 t4) =
    NatElim (substDown i r t1)
            (substDown i r t2)
            (substDown i r t3)
            (substDown i r t4)



test :: IO ()
test = do
{-
    pPrint $ quote (evalUp [] Star)
    pPrint $ quote (evalUp [] (Pi (Inf $ Free (Global "a")) (Inf $ Free (Global "a"))))
    putStrLn "////////////////"
    -}

    let id' =
            Ann
                (Lambda (Lambda (Inf $ Bound 0)))
                (Inf $ Pi (Inf Star) (Inf $ Pi (Inf $ Bound 0) (Inf $ Bound 1)))

        expr = App id' (Inf $ Free $ Global "Bool")
        expr2 = App expr (Inf $ Free $ Global "False")

    pPrint $ quote <$> typeUp [(Global "Bool", VStar), (Global "False", VNeutral (NFree $ Global "Bool"))] expr
    pPrint $ quote <$> typeUp [(Global "Bool", VStar), (Global "False", VNeutral (NFree $ Global "Bool"))] expr2
    pPrint $ quote $ evalUp emptyEnv expr2

    putStrLn "////////////////"

    let two = Inf $ Succ (Inf $ Succ $ Inf Zero)
        three = Inf $ Succ two
        plus =
            NatElim (Lambda (Inf (Pi (Inf Nat) (Inf Nat))))
                    (Lambda (Inf (Bound 0)))
                    (Lambda (Lambda (Lambda (Inf $ Succ $ Inf (App (Bound 1) (Inf $ Bound 0))))))
                    -- two


    pPrint $ quote $ evalUp emptyEnv (App (plus two) three)
    pPrint $ quote <$> typeUp [] (App (plus two) three)
    pPrint $ quote <$> typeUp [] (plus two)

    {- 

〉〉 let plus = natElim (λ → Nat → Nat)
(λn → n)
(λk rec n → Succ (rec n))
plus :: ∀(x :: Nat) (y :: Nat).Nat



    -}
