{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Repl where

import Control.Monad.State (MonadState, modify, StateT, liftIO, evalStateT, gets, evalState)
import DepLambda
import Text.Megaparsec (ParseErrorBundle)
import Data.Text (Text)
import Data.Void (Void)
import qualified DepParser as Parser
import qualified Streamly.Prelude as Stream
import qualified Data.List.NonEmpty as NE
import qualified Streamly.Console.Stdio as Stdio
import qualified Streamly.Data.Fold as Fold
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified Streamly.Unicode.Stream as UniStream
import Data.Foldable (fold)
import Data.Coerce (coerce)
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty)
import Control.Monad.Except (MonadError, throwError, runExceptT, ExceptT)
import Control.Lens hiding (Context)
import Control.Monad.RWS (tell)
import Control.Monad.RWS.Strict (runRWS)
import Data.List (singleton)

data Error =
    ParseError (ParseErrorBundle Text Void)
    | CompilationError Text
    | TypeError Text
    deriving (Show)

data ReplState = RS
    { _rsContext :: Context
    , _rsBindings :: Bindings
    }

makeLenses ''ReplState
 
type ProgramStatement = Text




replEval
    :: forall m
    .  (MonadState ReplState m)
    => (ReplState -> EvalResult -> m ())
    -> (ReplState -> Error -> m ())
    -> ProgramStatement
    -> m ()
replEval reportResult reportError statement =
    runExceptT eval >>= report
    where
        eval :: ExceptT  Error m EvalResult
        eval = parse statement >>= evaluateStatement

        report :: Either Error EvalResult -> m ()
        report res = do
            s <- use id
            either (reportError s) (reportResult s) res

emptyContext :: Context
emptyContext = []

initialReplState :: ReplState
initialReplState = RS emptyContext emptyBindings

printingRepl :: Stream.SerialT (StateT ReplState IO) Text -> IO ()
printingRepl stream = 
    stream
        & Stream.mapM (replEval reportRes reportErr)
        & Stream.drain
        & flip evalStateT initialReplState
    where
        reportRes _ = liftIO . printEvalRes
        reportErr _ = liftIO . print


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


testRepl :: NonEmpty ProgramStatement -> NonEmpty (Either Error EvalResult, ReplState)
testRepl program = runRWS run () initialReplState ^. (_3.to NE.fromList)
    -- fixme slow to append lists
    where
      run = traverse (replEval saveResult saveError) program
      saveResult state res = tell . singleton $ (Right res, state)
      saveError state err = tell . singleton $ (Left err, state)

data EvalResult
    = EvAssumed (NonEmpty (Parser.Identifier, Value))
    | EvLet Parser.Identifier Type
    | EvRes Value (Maybe Type)

printEvalRes :: EvalResult -> IO ()
printEvalRes = TIO.putStrLn . showEvalRes

showEvalRes :: EvalResult -> Text
showEvalRes (EvAssumed results) = "Assumed: " <> names
    where names = fold $ NE.intersperse ", " ((identifier2text . (^. _1)) <$> results)
showEvalRes (EvRes val typ) = showValue val <> " :: " <> typeText
    where typeText = maybe "?" showValue typ
showEvalRes (EvLet name typ) = identifier2text name  <> " :: " <> showValue typ

identifier2text :: Parser.Identifier -> Text
identifier2text = coerce

parse :: (MonadError Error m) => ProgramStatement -> m Parser.Statement
parse statement =
    Parser.parseStatement statement
    & either
        (throwError . ParseError)
        pure

compile :: (MonadError Error m) => Parser.Expr -> m Expression
compile e =
    compileExpr e
    & either
        (throwError . CompilationError)
        pure

evaluateStatement :: (MonadState ReplState m, MonadError Error m) => Parser.Statement -> m EvalResult
evaluateStatement (Parser.StAssume items) = traverse assume items <&> EvAssumed

evaluateStatement (Parser.StExpr expr) = do
    (res, resType) <- compile expr >>= evalExpression 
    pure $ EvRes res resType


evaluateStatement (Parser.StLet name expr) = do
    compiledExpr <- compile expr
    -- fixme incomplete pattern
    (value, typ) <- evalExpression compiledExpr
    case typ of
        Nothing -> throwError $ TypeError "Cannot find type of let statement"
        Just typ' -> do
            modifying rsBindings ((coerce name, value):)
            modifying rsContext ((id2id name, typ'):)
            pure $ EvLet name typ'

evalExpression :: (MonadState ReplState m, MonadError Error m) => Expression -> m (Value, (Maybe Type))
evalExpression (ExprUp e) = do
    bs <- use rsBindings
    ctx <- use rsContext
    case typeUp ctx bs e of
        Left err -> throwError $ TypeError err
        Right typ -> pure $ (evalUp bs emptyEnv e, Just typ)

evalExpression (ExprDown e) = do
    bs <- use rsBindings
    pure $ (evalDown bs emptyEnv e, Nothing)



assume :: (MonadState ReplState m, MonadError Error m) => Parser.TypeAssume -> m (Parser.Identifier, Type)
assume  (Parser.TypeAssume n typ) = do
    compiled <- compile typ
    -- fixme incomplete pattern match
    (assumeType, _) <- evalExpression compiled
    modifying rsContext ((id2id n, assumeType):) $> (n, assumeType)


type NamePool = [Text]

acquireName :: MonadState NamePool m => m Text
acquireName = gets head <* modify tail

releaseName :: MonadState NamePool m => Text -> m ()
releaseName n =  modify (n:)

withName :: MonadState NamePool m => (Text -> m a) -> m a
withName f = acquireName >>= (\name -> f name <* releaseName name)


showDown :: MonadState NamePool m => NamePool -> TermDown -> m Text
showDown binding (Inf t) = showUp binding t
showDown binding (Lambda d) = do
    withName $ \var -> do
        body <- showDown (var:binding) d
        pure $ wrap var body
    where
        wrap var body = "λ" <> var <> " → " <> body

showUp :: MonadState NamePool m => NamePool -> TermUp -> m Text
showUp binding (Bound n) = pure (binding !! n)
showUp _ (Free name) = pure $ displayName name
showUp binding (Ann term typ) = do
    term' <- showDown binding term
    typ' <- showDown binding typ
    pure $ term' <> " :: " <> typ'


showUp binding (App f arg) = wrap <$> showUp binding f <*> showDown binding arg
    where
        wrap f' arg' = "(" <> f'  <> " " <> arg' <> ")"
showUp _ Star = pure "*"
showUp _ Nat = pure "Nat"
showUp _ Zero = pure "Zero"
showUp binding (NatElim a b c d) = do
    a' <- showDown binding a 
    b' <-  showDown binding b 
    c' <-  showDown binding c 
    d' <-  showDown binding d 
    pure $ "(natElim (" <> a' <> ") (" <> b' <> ") (" <> c' <> ") (" <> d' <> "))"
showUp binding (Succ a) = do 
    prev <- showDown binding a
    pure $ "Succ (" <> prev <> ")"
showUp binding (Pi from to) = do
    withName $ \var -> do
        f <- showDown (var:binding) from
        t <- showDown (var:binding) to
        pure $ "(∀ (" <> var <> " :: " <> f <> "). " <> t <> ")"
showUp binding (Nil alpha) = do
    a <- showDown binding alpha
    pure $ "(Nil " <> a <> ")"
showUp binding (Vec alpha n) = do
    a <- showDown binding alpha
    s <- showDown binding n
    pure $ "(Vec (" <> a <> ") (" <> s <> "))"
showUp binding (Cons a b c d) = do
    a' <- showDown binding a 
    b' <-  showDown binding b 
    c' <-  showDown binding c 
    d' <-  showDown binding d 
    pure $ "(Cons (" <> a' <> ") (" <> b' <> ") (" <> c' <> ") (" <> d' <> "))"
showUp binding (VecElim a b c d e f) = do
    a' <- showDown binding a 
    b' <-  showDown binding b 
    c' <-  showDown binding c 
    d' <-  showDown binding d 
    e' <-  showDown binding e 
    f' <-  showDown binding f 
    pure $ "(vecElim (" <> a' <> ") (" <> b' <> ") (" <> c' <> ") (" <> d' <> ") (" <> e' <> ") (" <> f' <> "))"

showExpression :: MonadState NamePool m => NamePool -> Expression -> m Text
showExpression pool (ExprUp term) = showUp pool term
showExpression pool (ExprDown term) = showDown pool term


displayName :: Name -> Text
displayName (Global t) = t
displayName (Local _) = error "local display"
displayName (Quote _) = error "quote display"


showValue :: Value -> Text
showValue term = evalState (showDown [] (quote term)) nameSource

nameSource :: NamePool
nameSource = usual ++ (("a" <>) .  Text.pack . show <$> [(1 :: Int)..])
    where usual = ["x", "y", "z", "u", "v", "w", "r", "s", "t"]
  

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

    putStrLn "///////////////////////////"
    basicRepl
        [ "assume (t1 :: *) (t2 :: *) (a :: t1)"
        , "a :: t2"
        ]
