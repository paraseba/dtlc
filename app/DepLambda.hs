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
import Numeric.Natural (Natural)

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

    | Vec TermDown TermDown   -- Vec :: Pi (α :: *). Pi (n :: Nat). *
    | Nil TermDown            -- Nil :: Pi (α :: *). Vec α Zero
    | Cons TermDown           -- Cons :: Pi (α :: *).
           TermDown           --         Pi (n :: Nat).
           TermDown           --         α -> 
           TermDown           --         Vec α n ->
                              --         Vec α (Succ n)

    | VecElim TermDown        -- VecElim :: Pi (α :: *).
              TermDown        --            Pi (m :: Pi (k :: Nat). Vec α k -> *).
              TermDown        --            m Zero (Nil α) ->
              TermDown        --            Pi (k :: Nat). Pi (a :: α). Pi (as :: Vec α k). m k as -> m (Succ k) (Cons α k a as)
              TermDown        --            Pi (k :: Nat).
              TermDown        --            Pi xs :: Vec α k.
                              --            m k xs
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

    | VVec Value Value
    | VNil Value
    | VCons Value Value Value Value

data Neutral =
    NFree Name
    | NApp Neutral Value
    | NNatElim  Value Value Value Neutral
    | NVecElim  Value Value Value Value Value Neutral

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

evalUp env (Vec alpha n) = VVec (evalDown env alpha) (evalDown env n)
evalUp env (Nil alpha) = VNil (evalDown env alpha)
evalUp env (Cons alpha n a more) =
    VCons (evalDown env alpha) (evalDown env n)
          (evalDown env a) (evalDown env more)
evalUp env (VecElim alpha m mnil mcons k as) =
    iter kVal (evalDown env as)
    where
        iter _ (VNil _) = mnilVal
        iter _ (VCons _ n a more) =
            mconsVal `vapp` n `vapp` a `vapp` more `vapp` iter n more

        iter _ (VNeutral v') =
            VNeutral $ NVecElim alphaVal mVal mnilVal mconsVal kVal v'
            -- fixme why not store as too

        iter _ _ = error "Internal error, vecElim'ing not a vector"

        mnilVal = evalDown env mnil
        mconsVal = evalDown env mcons
        kVal = evalDown env k
        alphaVal = evalDown env alpha
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

quote' i (VVec alpha n) = Inf $ Vec (quote' i alpha) (quote' i n)
quote' i (VNil alpha) = Inf $ Nil (quote' i alpha)
quote' i (VCons alpha n a more) =
    Inf $ Cons (quote' i alpha) (quote' i n)
               (quote' i a) (quote' i more)

quoteNeutral :: Int -> Neutral -> TermUp
quoteNeutral i (NFree n) = replaceQuote i n
quoteNeutral i (NApp f arg) =
    App (quoteNeutral (i+1) f) (quote' (i+1) arg)

quoteNeutral i (NNatElim t1 t2 t3 n) =
    NatElim (quote' i t1)
            (quote' i t2)
            (quote' i t3)
            (Inf (quoteNeutral i n))

quoteNeutral i (NVecElim t1 t2 t3 t4 t5 n) =
    VecElim (quote' i t1)
            (quote' i t2)
            (quote' i t3)
            (quote' i t4)
            (quote' i t5)
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

typeUp' i ctx (Vec alpha n) = do
    typeDown' i ctx alpha VStar
    typeDown' i ctx n VNat
    pure VStar
typeUp' i ctx (Nil alpha) = do
    typeDown' i ctx alpha VStar
    pure $ VVec (evalDown emptyEnv alpha) VZero
typeUp' i ctx (Cons alpha n a more) = do
    typeDown' i ctx alpha VStar
    typeDown' i ctx n VNat
    typeDown' i ctx a alphaVal
    typeDown' i ctx more (VVec alphaVal nVal)
    pure $ VVec alphaVal (VSucc nVal)
    -- why not checking relationship between n and more or that n > 0
    where
        nVal = evalDown emptyEnv n
        alphaVal = evalDown emptyEnv alpha
typeUp' i ctx (VecElim alpha m mnil mcons k as) = do --fixme
    typeDown' i ctx alpha VStar
    typeDown' i ctx m (VPi VNat (\n -> VPi (VVec alphaVal n) (const VStar)))
    let tau = mVal `vapp` VZero `vapp` VNil alphaVal
    typeDown' i ctx mnil tau
    typeDown' i ctx mcons
              (VPi VNat $ \l ->
                VPi alphaVal $ \a ->
                VPi (VVec alphaVal l) $ \xs ->
                VPi (mVal `vapp` l `vapp` xs) $ \_ ->
                mVal `vapp` VSucc l `vapp` VCons alphaVal l a xs
              )
    typeDown' i ctx k VNat
    typeDown' i ctx as (VVec alphaVal kVal)
    pure $ mVal `vapp` kVal `vapp` asVal
    where
        mVal = evalDown [] m
        alphaVal = evalDown [] alpha
        kVal = evalDown [] k
        asVal = evalDown [] as

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

substUp i r (Vec alpha n) = Vec (substDown i r alpha) (substDown i r n)
substUp i r (Nil alpha) = Nil (substDown i r alpha)
substUp i r (Cons alpha n a more) =
    Cons (substDown i r alpha) (substDown i r n)
    (substDown i r a) (substDown i r more)

substUp i r (VecElim t1 t2 t3 t4 t5 t6) =
    VecElim (substDown i r t1)
            (substDown i r t2)
            (substDown i r t3)
            (substDown i r t4)
            (substDown i r t5)
            (substDown i r t6)


nat2nat :: Natural -> TermUp
nat2nat 0 = Zero
nat2nat n = Succ $ Inf $ nat2nat (n - 1)
-- nat2nat n = Succ $ iterate (Inf . Succ) (Inf Zero) !! (fromIntegral n - 1)

test :: IO ()
test = do
{-
    pPrint $ quote (evalUp [] Star)
    pPrint $ quote (evalUp [] (Pi (Inf $ Free (Global "a")) (Inf $ Free (Global "a"))))
    putStrLn "////////////////"
    -}
    pPrint $ nat2nat 0
    pPrint $ nat2nat 1
    pPrint $ nat2nat 2
    pPrint $ nat2nat 3

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

    let two = Inf $ nat2nat 2
        three = Inf $ nat2nat 3
        plus =
            NatElim (Lambda (Inf (Pi (Inf Nat) (Inf Nat))))
                    (Lambda (Inf (Bound 0)))
                    (Lambda (Lambda (Lambda (Inf $ Succ $ Inf (App (Bound 1) (Inf $ Bound 0))))))
                    -- two


    pPrint $ quote $ evalUp emptyEnv (App (plus two) three)
    pPrint $ quote <$> typeUp [] (App (plus two) three)
    pPrint $ quote <$> typeUp [] (plus two)

    
    putStrLn "////////////////"


