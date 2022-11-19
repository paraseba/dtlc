{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE FlexibleContexts #-}

module Lambda where

import Control.Monad.Except (throwError)
import Data.Functor (($>))
import Control.Monad (unless)
import Text.Megaparsec (runParser, ParseErrorBundle)
import qualified Parser
import Text.Pretty.Simple (pPrint)
import Control.Monad.State (MonadState, get, modify, evalStateT, liftIO, evalState, gets, StateT)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Foldable (Foldable (foldl'), toList, fold)
import Prelude hiding (exp)
import qualified Data.List.NonEmpty as NE
import Data.List (elemIndex)
import Data.Void (Void)
import Control.Lens hiding (Context, from, to)
import qualified Data.Text.IO as TIO
import Data.Coerce (coerce)
import qualified Streamly.Prelude as Stream
import qualified Streamly.Console.Stdio as Stdio
import qualified Streamly.Unicode.Stream as UniStream
import qualified Streamly.Data.Fold as Fold

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
    Global Text
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
quoteNeutral i (NFree n) = replaceQuote i n
quoteNeutral i (NApp f arg) = App (quoteNeutral (i+1) f) (quote' (i+1) arg)

replaceQuote :: Int -> Name -> TermUp
replaceQuote i (Quote n) = Bound (i - n - 1)
replaceQuote _ x = Free x

data Kind = Star
    deriving (Show, Eq)

data TypeInfo =
    HasType Type
    | HasKind Kind
    deriving (Show, Eq)

type Result a = Either Text a
type Context = [(Name, TypeInfo)]


isStar :: Context -> Type -> Result ()
isStar ctx (TFree n) =
    unless (lookup n ctx == Just (HasKind Star))
        (throwError $ "Not * Kind: " <> Text.pack (show n))

isStar ctx (TFun from to) = isStar ctx from *> isStar ctx to

typeUp :: Int -> Context -> TermUp -> Result Type
typeUp _ _ (Bound _) = throwError "This should never be called"

typeUp _ ctx (Free name) =
    case lookup name ctx of
        Just (HasType typ)  -> pure typ
        _ -> throwError $ "Name not found " <> Text.pack (show name)

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
typeDown i ctx (Lambda t) (TFun from to)  = typeDown
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



data EvalResult =
    EvAssumed (NE.NonEmpty Parser.Identifier)
    | EvRes Value Type
    | EvError Text

data Expression =
    ExprUp TermUp | ExprDown TermDown
    deriving Show


evaluateSt :: MonadState Context m => Parser.Statement -> m EvalResult
evaluateSt (Parser.StAssume items) = traverse assume items <&> EvAssumed

evaluateSt (Parser.StExpr expr) = do
    ctx <- get
    case compileExpr [] expr of
        Left err -> pure $ EvError err
        Right compiledExpr ->
            case compiledExpr of
                ExprUp e ->
                    case typeUp 0 ctx e of
                        Left err -> pure $ EvError err
                        Right typ -> do
                            let val = evalUp e []
                            pure $ EvRes val typ
                ExprDown e -> do
                    let val = evalDown e []
                    pure $ EvRes val (TFree (Global "unknown"))



assume :: MonadState Context m => Parser.AssumeItem -> m Parser.Identifier
assume  (Parser.TypeAssume n typ) =
    modify ((id2id n, HasType $ type2type typ):) $> n

assume  (Parser.KindAssume n@(Parser.Identifier name)) =
    modify ((Global name, HasKind Star):) $> n

id2id :: Parser.Identifier -> Name
id2id (Parser.Identifier name) = Global name

type2type :: Parser.Type -> Type
type2type (Parser.TId n) = TFree $ id2id n
type2type (Parser.TFun from to) = TFun (type2type from) (type2type to)

type CompilationResult a = Either Text a
type Bindings = [Parser.Identifier]

compileExpr :: Bindings -> Parser.Expr -> CompilationResult Expression
compileExpr bs (Parser.Var n) =
    pure . ExprUp $ replacement
    where replacement =
            case elemIndex n bs of
                Nothing -> Free $ id2id n
                Just i -> Bound i

compileExpr bs (Parser.Ann exp typ) = do
    term <- compileExpr bs exp
    pure $ ExprUp (Ann (toTermDown term) (type2type typ))

compileExpr bs (Parser.App f args) = do
  argTerms <- traverse (fmap toTermDown . compileExpr bs) args
  fTerm <- compileExpr bs f >>= toTermUp
  -- fixme should this be foldl' ?
  pure . ExprUp $ foldl' App fTerm argTerms

compileExpr bs (Parser.Lambda ids body) =
    compileLambda bs ids body


compileLambda :: Bindings -> NE.NonEmpty Parser.Identifier -> Parser.Expr -> CompilationResult Expression
compileLambda bs ids body =
    wrap <$> compileExpr newBindings body
    where
        newBindings = reverse (toList ids) <> bs

        wrap exp = iterate (ExprDown . Lambda . toTermDown) exp !! length ids



expandMultiArgs :: NE.NonEmpty Parser.Identifier -> Parser.Expr -> Parser.Expr
expandMultiArgs ids body = foldr go body ids
    where go arg = Parser.Lambda (NE.singleton arg)


toTermDown :: Expression -> TermDown
toTermDown (ExprDown d) = d
toTermDown (ExprUp u) = Inf u

toTermUp :: Expression -> CompilationResult TermUp
toTermUp (ExprDown (Inf e)) = pure e --fixme is it OK to make this transformation? am I losing the type info?
toTermUp (ExprDown _) = throwError "Lambdas must be annotated with their type"
toTermUp (ExprUp u) = pure u


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


type NamePool = [Text]

displayDown :: MonadState NamePool m => NamePool -> TermDown -> m Text
displayDown binding (Inf t) = displayUp binding t
displayDown binding (Lambda d) = do
    var <- gets head
    modify tail -- reserve the name
    body <- displayDown (var:binding) d
    modify (var:)  -- return the name to the pool
    pure $ wrap var body
    where
        wrap var body = "λ" <> var <> " → " <> body

displayUp :: MonadState NamePool m => NamePool -> TermUp -> m Text
displayUp binding (Bound n) = pure (binding !! n)
displayUp _ (Free name) = pure $ displayName name
displayUp binding (Ann term typ) =
    displayDown binding term <&> (<> " :: " <> displayType typ)


displayUp binding (App f arg) = wrap <$> displayUp binding f <*> displayDown binding arg
    where
        wrap f' arg' = "(" <> f'  <> " " <> arg' <> ")"

displayType :: Type -> Text
displayType (TFree n) = displayName n
displayType (TFun from to) = "(" <> displayType from <> " → " <> displayType to <> ")"


displayName :: Name -> Text
displayName (Global t) = t
displayName (Local _) = error "local display"
displayName (Quote _) = error "quote display"



display :: TermDown -> Text
display term = evalState (displayDown [] term) nameSource

nameSource :: NamePool
nameSource = usual ++ (("a" <>) .  Text.pack . show <$> [(1 :: Int)..])
    where usual = ["x", "y", "z", "u", "v", "w", "r", "s", "t"]
  


printEvalRes :: EvalResult -> IO ()
printEvalRes (EvAssumed ids) = TIO.putStrLn $ "Assumed: " <> names
    where names = fold $ NE.intersperse ", " (identifier2text <$> ids)
printEvalRes (EvError err) = putStrLn $ "Error: " <> show err
printEvalRes (EvRes val typ) =
    TIO.putStrLn $ display (quote val) <> " :: " <> displayType typ

identifier2text :: Parser.Identifier -> Text
identifier2text = coerce

-- samples
id' :: TermDown
id' = Lambda (Inf (Bound 0))

const' :: TermDown
const' = Lambda (Lambda (Inf (Bound 1)))


tfree :: Text -> Type
tfree alpha = TFree (Global alpha)

free :: Text -> TermDown
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

    let parse = runParser Parser.assumeParser "input"
        parseType = runParser Parser.typeParser "input"
        parseExpr = runParser (Parser.exprParser <* Parser.lineEnd) "input"
        parseStatement = runParser Parser.statementParser "input"

    print $ parse "assume aaa ::  *"
    print $ parse "assume bbb ::  mytype   "
    print $ parse "assume ccc ::  yourtype   \n"
    print $ parse "assume ccc ::  mytype -> (yourtype -> yourtype)   \n"
    print $ parse "assume (aaa ::  *)"
    print $ parse "assume (bbb ::  *)   "
    print $ parse "assume (ccc ::  *)   \n"
    print $ parse "assume   (aaa ::  *) (ddd ::  sometype)"
    print $ parse "assume   (bbb ::  *)(ddd ::  *)   "
    print $ parse "assume (ccc ::  *) (ddd ::  sometype)(eee ::  *) \n"

    print $ parseExpr "\\foo -> foo"
    print $ parseExpr "\\ foo bar baz -> foo"
    print $ parseExpr "\\ foo bar baz -> (\\ x -> x)"
    print $ parseExpr "\\ foo bar baz -> \\ x -> x"
    print $ parseExpr "a"
    print $ parseExpr "a "
    print $ parseExpr "a b"

    pPrint $ parseExpr "(\\a b -> b) a b"
    pPrint $ parseExpr "(\\a b -> b) (a b) c"
    pPrint $ parseExpr "a b c"
    pPrint $ parseExpr "(\\ foo bar baz -> foo) b "
    pPrint $ parseExpr "(\\ foo bar baz -> foo) b c"
    pPrint $ parseExpr "(\\ foo bar baz -> foo) (\\x -> x) c"


    pPrint $ parseType "baz"
    pPrint $ parseType "foo  ->  bar  "
    pPrint $ parseType "foo  ->  bar->baz"
    pPrint $ parseType "(baz)"
    pPrint $ parseType "(foo -> (baz))"
    pPrint $ parseType "(foo -> baz) -> res"


    pPrint $ parseExpr "foo :: bar"
    pPrint $ parseExpr "foo :: bar -> baz"
    pPrint $ parseExpr "((\\x y -> x) :: (bar -> baz -> bar)) (a b) (c :: ctype)"

    pPrint $ parseStatement "   ((\\x y -> x) :: (bar -> baz -> bar)) (a b) (c :: ctype)   \n "
    pPrint $ parseStatement "   assume (ccc ::  *) (ddd ::  sometype)(eee ::  *) \n"

    --- fixme space before input

    pPrint $ expandMultiArgs ["x"] (Parser.Var "x")
    pPrint $ expandMultiArgs ["x", "y"] (Parser.Var "x")
    pPrint $ expandMultiArgs ["x", "y", "z"] (Parser.Lambda ["w"] (Parser.Var "y"))

    pPrint $ compileExpr [] (Parser.Var "x")
    pPrint $ compileExpr [] (Parser.Ann (Parser.Var "x") (Parser.TId "foo") )
    pPrint $ compileExpr [] (Parser.Lambda ["x"] (Parser.Var "x")  )
    pPrint $ compileExpr [] (Parser.Lambda ["x"] (Parser.Var "y")  )
    pPrint $ compileExpr [] (Parser.Lambda ["x", "y"] (Parser.Var "x")  )
    pPrint $ compileExpr [] (Parser.Lambda ["x", "y"] (Parser.Var "y")  )
    pPrint $ compileExpr [] (Parser.Lambda ["x", "y"] (Parser.Lambda ["x"] (Parser.Var "x"))  )
    pPrint $ compileExpr [] (Parser.App (Parser.Lambda ["x", "y"] (Parser.Lambda ["x"] (Parser.Var "x"))  ) [Parser.Var "x", Parser.Var "y"] )


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
