{-# LANGUAGE OverloadedStrings #-}

module DTLC.Lambda where

import Control.Lens hiding (Context, from, to)
import Control.Monad (unless)
import Control.Monad.Except (throwError)
import DTLC.Parser qualified as P
import Data.Foldable (foldlM, toList)
import Data.Functor (($>))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Numeric.Natural (Natural)
import Prelude hiding (exp, pi)

data TermUp
    = Star
    | Bound Int
    | Free Name
    | Ann TermDown TermDown
    | App TermUp TermDown
    | Pi TermDown TermDown
    | Nat
    | Zero
    | Succ TermDown
    | NatElim
        TermDown -- NatElim :: Pi (m :: Nat -> Star).
        TermDown --            m Zero ->
        TermDown --            (Pi (l :: Nat). m l -> m (Succ l)) ->
        TermDown --            Pi (k :: Nat). m k
    | Vec TermDown TermDown -- Vec :: Pi (α :: *). Pi (n :: Nat). *
    | Nil TermDown -- Nil :: Pi (α :: *). Vec α Zero
    | Cons
        TermDown -- Cons :: Pi (α :: *).
        TermDown --         Pi (n :: Nat).
        TermDown --         α ->
        TermDown --         Vec α n ->
        --         Vec α (Succ n)
    | VecElim
        TermDown -- VecElim :: Pi (α :: *).
        TermDown --            Pi (m :: Pi (k :: Nat). Vec α k -> *).
        TermDown --            m Zero (Nil α) ->
        TermDown --            Pi (k :: Nat). Pi (a :: α). Pi (as :: Vec α k). m k as -> m (Succ k) (Cons α k a as)
        TermDown --            Pi (k :: Nat).
        TermDown --            Pi xs :: Vec α k. m k xs
        --            m k xs
    deriving (Show, Eq)

data TermDown
    = Inf TermUp
    | Lambda TermDown
    deriving (Show, Eq)

data Name
    = Global Text
    | Local Int
    | Quote Int
    deriving (Eq, Show)

data Value
    = VStar
    | VNeutral Neutral
    | VPi Value (Value -> Value)
    | VFun (Value -> Value)
    | VNat
    | VZero
    | VSucc Value
    | VVec Value Value
    | VNil Value
    | VCons Value Value Value Value

data Neutral
    = NFree Name
    | NApp Neutral Value
    | NNatElim Value Value Value Neutral
    | NVecElim Value Value Value Value Value Neutral

type Type = Value

type Env = [Value]
type Bindings = [(Text, Value)]

vapp :: Value -> Value -> Value
vapp (VFun f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalUp :: Bindings -> Env -> TermUp -> Value
evalUp _ _ Star = VStar
evalUp _ env (Bound n) = env !! n
evalUp bs _ (Free (Global name)) = fromMaybe (VNeutral $ NFree $ Global name) (lookup name bs)
evalUp _ _ (Free name) = VNeutral $ NFree name
evalUp bs env (Ann t _) = evalDown bs env t
evalUp bs env (App fterm arg) =
    case evalUp bs env fterm of
        VFun fvalue -> fvalue argEval
        n@(VNeutral _) -> vapp n argEval
        bad -> error $ "fixme: " <> show (quote bad)
  where
    argEval = evalDown bs env arg
evalUp bs env (Pi t t') =
    VPi (evalDown bs env t) (\arg -> evalDown bs (arg : env) t')
evalUp _ _ Nat = VNat
evalUp _ _ Zero = VZero
evalUp bs env (Succ n) = VSucc (evalDown bs env n)
evalUp bs env (NatElim m mz ms k) =
    case kVal of
        VZero -> mzVal
        VSucc l ->
            let rec = evalUp bs env (NatElim m mz ms (quote l))
             in msVal `vapp` l `vapp` rec
        VNeutral k' -> VNeutral $ NNatElim mVal mzVal msVal k'
        _ -> error "Internal error, natElim'ing not a number"
  where
    mzVal = evalDown bs env mz
    msVal = evalDown bs env ms
    kVal = evalDown bs env k
    mVal = evalDown bs env m
evalUp bs env (Vec alpha n) = VVec (evalDown bs env alpha) (evalDown bs env n)
evalUp bs env (Nil alpha) = VNil (evalDown bs env alpha)
evalUp bs env (Cons alpha n a more) =
    VCons
        (evalDown bs env alpha)
        (evalDown bs env n)
        (evalDown bs env a)
        (evalDown bs env more)
evalUp bs env (VecElim alpha m mnil mcons k as) =
    iter kVal (evalDown bs env as)
  where
    iter _ (VNil _) = mnilVal
    iter _ (VCons _ n a more) =
        mconsVal `vapp` n `vapp` a `vapp` more `vapp` iter n more
    iter _ (VNeutral v') =
        VNeutral $ NVecElim alphaVal mVal mnilVal mconsVal kVal v'
    -- fixme why not store as too

    iter _ _ = error "Internal error, vecElim'ing not a vector"

    mnilVal = evalDown bs env mnil
    mconsVal = evalDown bs env mcons
    kVal = evalDown bs env k
    alphaVal = evalDown bs env alpha
    mVal = evalDown bs env m

evalDown :: Bindings -> Env -> TermDown -> Value
evalDown bs env (Lambda t) =
    VFun (\arg -> evalDown bs (arg : env) t)
evalDown bs env (Inf t) = evalUp bs env t

emptyEnv :: Env
emptyEnv = []

emptyBindings :: Bindings
emptyBindings = []

quote :: Value -> TermDown
quote = quote' 0

quote' :: Int -> Value -> TermDown
quote' _ VStar = Inf Star
quote' i (VNeutral n) = Inf $ quoteNeutral i n
quote' i (VFun f) =
    Lambda $ quote' (i + 1) $ f (VNeutral (NFree (Quote i)))
quote' i (VPi v f) =
    Inf $ Pi (quote' i v) $ quote' (i + 1) $ f (VNeutral (NFree (Quote i)))
quote' _ VNat = Inf Nat
quote' _ VZero = Inf Zero
quote' i (VSucc n) = Inf (Succ $ quote' i n)
quote' i (VVec alpha n) = Inf $ Vec (quote' i alpha) (quote' i n)
quote' i (VNil alpha) = Inf $ Nil (quote' i alpha)
quote' i (VCons alpha n a more) =
    Inf $
        Cons
            (quote' i alpha)
            (quote' i n)
            (quote' i a)
            (quote' i more)

quoteNeutral :: Int -> Neutral -> TermUp
quoteNeutral i (NFree n) = replaceQuote i n
quoteNeutral i (NApp f arg) =
    App (quoteNeutral (i + 1) f) (quote' (i + 1) arg)
quoteNeutral i (NNatElim t1 t2 t3 n) =
    NatElim
        (quote' i t1)
        (quote' i t2)
        (quote' i t3)
        (Inf (quoteNeutral i n))
quoteNeutral i (NVecElim t1 t2 t3 t4 t5 n) =
    VecElim
        (quote' i t1)
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

typeUp :: Context -> Bindings -> TermUp -> TypingResult Type
typeUp = typeUp' 0

typeUp' :: Int -> Context -> Bindings -> TermUp -> TypingResult Type
typeUp' _ _ _ (Bound _) = throwError "This should never be called"
typeUp' _ ctx _ (Free name) =
    case lookup name ctx of
        Just typ -> pure typ
        _ -> throwError $ "Name not found " <> Text.pack (show name)
typeUp' i ctx bs (Ann e rho) = do
    typeDown' i ctx bs rho VStar
    let tau = evalDown bs emptyEnv rho
    typeDown' i ctx bs e tau
    pure tau
typeUp' _ _ _ Star = pure VStar
typeUp' i ctx bs (App e e') = do
    ftype <- typeUp' i ctx bs e
    case ftype of
        VPi tau tau' -> do
            typeDown' i ctx bs e' tau
            pure $ tau' (evalDown bs emptyEnv e')
        _ -> throwError "Invalid application"
typeUp' i ctx bs (Pi rho rho') = do
    typeDown' i ctx bs rho VStar
    let tau = evalDown bs emptyEnv rho
    typeDown' (i + 1) ((Local i, tau) : ctx) bs (substDown 0 (Free (Local i)) rho') VStar
    pure VStar
typeUp' _ _ _ Nat = pure VStar
typeUp' _ _ _ Zero = pure VNat
typeUp' i ctx bs (Succ n) = typeDown' i ctx bs n VNat $> VNat
typeUp' i ctx bs (NatElim m mz ms k) = do
    typeDown' i ctx bs m (VPi VNat (const VStar))
    let tau = mVal `vapp` VZero
    typeDown' i ctx bs mz tau
    typeDown' i ctx bs k VNat
    typeDown' i ctx bs ms (VPi VNat (\l -> VPi (mVal `vapp` l) (\_ -> mVal `vapp` VSucc l)))
    pure (mVal `vapp` kVal)
  where
    mVal = evalDown bs [] m
    kVal = evalDown bs [] k
typeUp' i ctx bs (Vec alpha n) = do
    typeDown' i ctx bs alpha VStar
    typeDown' i ctx bs n VNat
    pure VStar
typeUp' i ctx bs (Nil alpha) = do
    typeDown' i ctx bs alpha VStar
    pure $ VVec (evalDown bs emptyEnv alpha) VZero
typeUp' i ctx bs (Cons alpha n a more) = do
    typeDown' i ctx bs alpha VStar
    typeDown' i ctx bs n VNat
    typeDown' i ctx bs a alphaVal
    typeDown' i ctx bs more (VVec alphaVal nVal)
    pure $ VVec alphaVal (VSucc nVal)
  where
    -- why not checking relationship between n and more or that n > 0

    nVal = evalDown bs emptyEnv n
    alphaVal = evalDown bs emptyEnv alpha
typeUp' i ctx bs (VecElim alpha m mnil mcons k as) = do
    -- fixme
    typeDown' i ctx bs alpha VStar
    typeDown' i ctx bs m (VPi VNat (\n -> VPi (VVec alphaVal n) (const VStar)))
    let tau = mVal `vapp` VZero `vapp` VNil alphaVal
    typeDown' i ctx bs mnil tau
    typeDown'
        i
        ctx
        bs
        mcons
        ( VPi VNat $ \l ->
            VPi alphaVal $ \a ->
                VPi (VVec alphaVal l) $ \xs ->
                    VPi (mVal `vapp` l `vapp` xs) $ \_ ->
                        mVal `vapp` VSucc l `vapp` VCons alphaVal l a xs
        )
    typeDown' i ctx bs k VNat
    typeDown' i ctx bs as (VVec alphaVal kVal)
    pure $ mVal `vapp` kVal `vapp` asVal
  where
    mVal = evalDown bs [] m
    alphaVal = evalDown bs [] alpha
    kVal = evalDown bs [] k
    asVal = evalDown bs [] as

typeDown :: Context -> Bindings -> TermDown -> Type -> TypingResult ()
typeDown = typeDown' 0

typeDown' :: Int -> Context -> Bindings -> TermDown -> Type -> TypingResult ()
typeDown' i ctx bs (Lambda e) (VPi tau tau') =
    typeDown'
        (i + 1)
        ((Local i, tau) : ctx)
        bs
        (substDown 0 (Free (Local i)) e)
        (tau' (VNeutral (NFree (Local i))))
typeDown' _ _ _ (Lambda _) x = throwError $ "Cannot type lambda: " <> Text.pack (show (quote x))
typeDown' i ctx bs (Inf e) v = do
    actual <- typeUp' i ctx bs e
    unless ((quote actual) == (quote v)) $
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
    App
        (substUp i replacement fterm)
        (substDown i replacement argterm)
substUp i replacement (Pi tau tau') =
    Pi (substDown i replacement tau) (substDown (i + 1) replacement tau')
substUp _ _ Nat = Nat
substUp _ _ Zero = Zero
substUp i r (Succ n) = Succ $ substDown i r n
substUp i r (NatElim t1 t2 t3 t4) =
    NatElim
        (substDown i r t1)
        (substDown i r t2)
        (substDown i r t3)
        (substDown i r t4)
substUp i r (Vec alpha n) = Vec (substDown i r alpha) (substDown i r n)
substUp i r (Nil alpha) = Nil (substDown i r alpha)
substUp i r (Cons alpha n a more) =
    Cons
        (substDown i r alpha)
        (substDown i r n)
        (substDown i r a)
        (substDown i r more)
substUp i r (VecElim t1 t2 t3 t4 t5 t6) =
    VecElim
        (substDown i r t1)
        (substDown i r t2)
        (substDown i r t3)
        (substDown i r t4)
        (substDown i r t5)
        (substDown i r t6)

nat2nat :: Natural -> TermUp
nat2nat 0 = Zero
nat2nat n = Succ $ Inf $ nat2nat (n - 1)

-- nat2nat n = Succ $ iterate (Inf . Succ) (Inf Zero) !! (fromIntegral n - 1)

type CompilationResult a = Either Text a
type LambdaBindings = [P.Identifier]

data Expression
    = ExprUp TermUp
    | ExprDown TermDown
    deriving (Eq, Show)

bound :: Int -> TermDown
bound n = Inf (Bound n)

pi :: TermUp -> TermUp -> TermDown
pi a b = Inf $ Pi (Inf a) (Inf b)

pid :: TermUp -> TermDown -> TermDown
pid a b = Inf $ Pi (Inf a) b

compileExpr :: P.Expr -> CompilationResult Expression
compileExpr = compileExpr' []

compileExpr' :: LambdaBindings -> P.Expr -> CompilationResult Expression
compileExpr' _ P.Star = pure $ ExprUp Star
compileExpr' _ (P.LiteralNat n) = pure . ExprUp . nat2nat $ n
compileExpr' bs (P.Var n) =
    case n of
        "Nat" -> pure $ ExprUp Nat
        "Zero" -> pure $ ExprUp Zero
        "Succ" -> pure $ ExprUp (Ann succTerm succType)
        "Vec" -> pure $ ExprUp (Ann vecTerm vecType)
        "Nil" -> pure $ ExprUp (Ann nilTerm nilType)
        "Cons" -> pure $ ExprUp (Ann consTerm consType)
        "natElim" -> pure $ ExprUp (Ann natElimTerm natElimType)
        "vecElim" -> pure $ ExprUp (Ann vecElimTerm vecElimType)
        _ -> pure . ExprUp $ replacement
  where
    replacement =
        case elemIndex n bs of
            Nothing -> Free $ id2id n
            Just i -> Bound i
    succTerm = Lambda (Inf (Succ (bound 0)))
    succType = pi Nat Nat
    vecTerm = Lambda (Lambda (Inf $ Vec (bound 1) (bound 0)))
    vecType = pid Star (pi Nat Star)
    nilTerm = Lambda (Inf $ Nil (bound 0))
    nilType = pi Star (Vec (bound 0) (Inf Zero))
    consTerm = Lambda $ Lambda $ Lambda $ Lambda $ Inf $ Cons (bound 3) (bound 2) (bound 1) (bound 0)
    consType =
        pid
            Star
            ( pid
                Nat
                ( pid
                    (Bound 1)
                    ( pi
                        (Vec (bound 2) (bound 1))
                        (Vec (bound 3) (Inf $ Succ $ bound 2))
                    )
                )
            )
    natElimTerm = Lambda $ Lambda $ Lambda $ Lambda $ Inf $ NatElim (bound 3) (bound 2) (bound 1) (bound 0)
    natElimType =
        pid
            (Pi (Inf Nat) (Inf Star))
            ( pi
                (App (Bound 0) (Inf Zero))
                ( Pi
                    (pid Nat (pi (App (Bound 2) (bound 0)) (App (Bound 3) (Inf $ Succ $ bound 1))))
                    ( pi
                        Nat
                        (App (Bound 3) (bound 0))
                    )
                )
            )
    vecElimTerm = Lambda $ Lambda $ Lambda $ Lambda $ Lambda $ Lambda $ Inf $ VecElim (bound 5) (bound 4) (bound 3) (bound 2) (bound 1) (bound 0)
    vecElimType =
        pid Star $ -- alpha
            pid vecElimMType $ -- m
                pid vecElimMNilType $ -- mnil
                    pid vecElimConsType $ -- mcons
                        pid Nat $ -- k
                            pi
                                (Vec (bound 4) (bound 0)) -- xs
                                vecElimReturnType -- m k xs
    vecElimMType =
        Pi
            (Inf $ Nat) -- k
            (pi (Vec (bound 1) (bound 0)) Star) -- Vec alpha k -> *
    vecElimMNilType = App (App (Bound 0) (Inf $ Zero)) (Inf $ Nil (bound 1)) -- m Zero (Nil alpha)
    vecElimConsType =
        Pi (Inf $ Nat) $ -- l
            Inf $
                Pi (bound 3) $ -- x
                    Inf $
                        Pi (Inf $ Vec (bound 4) (bound 1)) $ -- xs
                            pi (App (App (Bound 4) (bound 2)) (bound 0)) $ -- m l xs
                                ( App -- m (Succ l) (Cons alpha l x xs)
                                    (App (Bound 5) (Inf $ Succ (bound 3)))
                                    (Inf $ Cons (bound 6) (bound 3) (bound 2) (bound 1))
                                )
    vecElimReturnType = App (App (Bound 4) (bound 1)) (bound 0) -- m k xs
compileExpr' bs (P.Ann exp typ) =
    make <$> compileExpr' bs exp <*> compileExpr' bs typ
  where
    make term ty =
        ExprUp (Ann (toTermDown term) (toTermDown ty))

-- fixme wrong number of args

compileExpr' bs (P.App f arg) = do
    argTerm <- fmap toTermDown . compileExpr' bs $ arg
    fTerm <- compileExpr' bs f >>= toTermUp
    pure . ExprUp $ App fTerm argTerm
compileExpr' bs (P.Function from to) =
    (\from' to' -> ExprUp $ Pi (toTermDown from') (toTermDown to'))
        <$> compileExpr' bs from
        <*> compileExpr' ("" : bs) to -- the range needs to bind parameters one step farther
compileExpr' bs (P.Pi args body) =
    compilePi bs args body
compileExpr' bs (P.Lambda ids body) =
    compileLambda bs ids body

-- fixme error on App of reserved words (Vec, Nil, etc) if they have zero args, that is, if they are Vars

compileLambda :: LambdaBindings -> NonEmpty P.Identifier -> P.Expr -> CompilationResult Expression
compileLambda bs ids body =
    wrap <$> compileExpr' newBindings body
  where
    newBindings = reverse (toList ids) <> bs
    wrap exp = iterate (ExprDown . Lambda . toTermDown) exp !! length ids

compilePi :: LambdaBindings -> NonEmpty (P.Identifier, P.Expr) -> P.Expr -> CompilationResult Expression
compilePi bs args body = do
    compiledArgTypes <- over mapped (reverse . fst) $ foldlM go' ([], bs) args

    -- let xx = compiledArgTypes ^. (_Right._1.Control.Lens.to reverse)
    compileExpr' newBindings body <&> wrap compiledArgTypes
  where
    newBindings = args ^.. reversed . folded . _1 <> bs

    wrap :: [Expression] -> Expression -> Expression
    wrap argTypes exp = foldr go exp argTypes

    go' :: ([Expression], LambdaBindings) -> (P.Identifier, P.Expr) -> CompilationResult ([Expression], LambdaBindings)
    go' (compiled, currentBindings) (ident, typ) = do
        t <- compileExpr' currentBindings typ
        pure (t : compiled, ident : currentBindings)

    go :: Expression -> Expression -> Expression
    go exp res = ExprUp $ Pi (toTermDown exp) (toTermDown res)

toTermDown :: Expression -> TermDown
toTermDown (ExprDown d) = d
toTermDown (ExprUp u) = Inf u

toTermUp :: Expression -> CompilationResult TermUp
toTermUp (ExprDown (Inf e)) = pure e -- fixme is it OK to make this transformation? am I losing the type info?
toTermUp (ExprDown _) = throwError "Lambdas must be annotated with their type"
toTermUp (ExprUp u) = pure u

id2id :: P.Identifier -> Name
id2id (P.Identifier name) = Global name
