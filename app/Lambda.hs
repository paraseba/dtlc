module Lambda where

import Control.Monad.Except (throwError)
import Data.Functor (($>))
import Control.Monad (unless)

data TermUp =
    Bound Int
    | Free Name
    | Ann TermDown Type
    | App TermUp TermDown
    deriving (Show)

data TermDown =
    Inf TermUp
    | Lambda TermDown
    deriving (Show)


data Name =
    Global String
    | Local Int
    | Quote Int
    deriving (Eq, Show)

data Value =
    VFun (Value -> Value)
    | VNeutral Neutral

data Neutral =
    NFree Name
    | NApp Neutral Value

data Type =
    TFree Name
    | TFun Type Type
    deriving (Eq, Show)

type Env = [Value]

evalUp :: TermUp -> Env -> Value
evalUp (Bound n) env = env !! n
evalUp (Free name) _ = VNeutral $ NFree name
evalUp (Ann t _) env = evalDown t env
evalUp (App fterm arg) env =
     case evalUp fterm env of
         VFun fvalue -> fvalue argEval
         VNeutral n -> VNeutral (NApp n argEval)
    where argEval = evalDown arg env


evalDown :: TermDown -> Env -> Value
evalDown (Lambda t) env =
    VFun $ \v -> evalDown t (v : env)

evalDown (Inf t) env = evalUp t env

quote :: Value -> TermDown
quote = quote' 0


quote' :: Int -> Value -> TermDown
quote' i (VNeutral n) = Inf $ quoteNeutral i n
quote' i (VFun f) = Lambda $ quote' (i+1) $ f (VNeutral (NFree (Quote i)))

quoteNeutral :: Int -> Neutral -> TermUp
quoteNeutral _ (NFree n) = Free n
quoteNeutral i (NApp f arg) = App (quoteNeutral (i+1) f) (quote' (i+1) arg)

data Kind = Star
    deriving (Show, Eq)

data TypeInfo =
    HasType Type
    | HasKind Kind
    deriving (Show, Eq)

type Result a = Either String a
type Context = [(Name, TypeInfo)]


isStar :: Context -> Type -> Result ()
isStar ctx (TFree n) =
    unless (lookup n ctx == Just (HasKind Star))
        (throwError $ "Not * Kind: " <> show n)

isStar ctx (TFun from to) = isStar ctx from *> isStar ctx to

typeUp :: Int -> Context -> TermUp -> Result Type
typeUp _ _ (Bound _) = throwError "This should never be called"

typeUp _ ctx (Free name) = 
    case lookup name ctx of
        Just (HasType typ)  -> pure typ
        _ -> throwError $ "Name not found " <> show name

typeUp i ctx (Ann term typ) = do
    isStar ctx typ
    typeDown i ctx term typ
    pure typ

typeUp i ctx (App fterm arg) = do
    ftype <- typeUp i ctx fterm
    case ftype of
        TFun fromType toType -> typeDown i ctx arg fromType $> toType
        _ -> throwError "Invalid application"
    

typeDown :: Int -> Context -> TermDown -> Type -> Result ()
typeDown i ctx (Lambda t) (TFun from to)  = do
    typeDown
        (i + 1)
        ((Local i, HasType from) : ctx)
        (substDown 0 (Free (Local i)) t)
        to

typeDown _ _tx (Lambda _) _  = throwError "Cannot type lambda"

typeDown i ctx (Inf t) typ = do
    actual <- typeUp i ctx t
    unless (actual == typ) (throwError "Invalid type")

substDown :: Int -> TermUp -> TermDown -> TermDown
substDown i replacement (Lambda t) =
    Lambda (substDown (i + 1) replacement t)

substDown i replacement (Inf t) =
    Inf (substUp i replacement t)

substUp :: Int -> TermUp -> TermUp -> TermUp
substUp i replacement (Bound n)
    | i == n = replacement
    | otherwise = Bound n
    
substUp _ _ (Free name) = Free name

substUp i replacement (Ann term typ) =
    Ann (substDown i replacement term) typ

substUp i replacement (App fterm argterm) =
    App (substUp i replacement fterm)
        (substDown i replacement argterm)


-- samples
id' :: TermDown
id' = Lambda (Inf (Bound 0))

const' :: TermDown
const' = Lambda (Lambda (Inf (Bound 1)))


tfree :: String -> Type
tfree alpha = TFree (Global alpha)

free :: String -> TermDown
free x = Inf (Free (Global x))


term1 :: TermUp
term1 = App (Ann id' (TFun (tfree "a") (tfree "a")) )
            (free "y")

term2 :: TermUp
term2 = App
            (App
                (Ann const' (TFun (TFun (tfree "b") (tfree "b"))
                                  (TFun (tfree "a") (TFun (tfree "b") (tfree "b")))))
                id')
            (free "y")

ctx1 :: Context
ctx1 = [(Global "y", HasType (tfree "a")), (Global "a", HasKind Star)]

ctx2 :: Context
ctx2 = (Global "b", HasKind Star) : ctx1

test :: IO ()
test = do
     
    print $ quote $ evalDown id' []
    print $ quote $ evalDown const' []
    print $ quote $ evalUp term1 []
    print $ quote $ evalUp term2 []
    print $ typeUp 0 ctx1 term1
    print $ typeUp 0 ctx2 term2


