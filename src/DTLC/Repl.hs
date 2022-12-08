{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module DTLC.Repl where

import Control.Lens hiding (Context)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Control.Monad.RWS (tell)
import Control.Monad.RWS.Strict (runRWS)
import Control.Monad.State (MonadState, StateT, evalState, evalStateT, gets, liftIO, modify)
import DTLC.Lambda qualified as L
import DTLC.Parser qualified as Parser
import Data.Coerce (coerce)
import Data.Foldable (fold)
import Data.Functor (($>))
import Data.List (singleton)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as TIO
import Data.Void (Void)
import Streamly.Console.Stdio qualified as Stdio
import Streamly.Data.Fold qualified as Fold
import Streamly.Prelude qualified as Stream
import Streamly.Unicode.Stream qualified as UniStream
import Text.Megaparsec (ParseErrorBundle)

data Error
    = ParseError (ParseErrorBundle Text Void)
    | CompilationError Text
    | TypeError Text
    deriving (Show)

data ReplState = RS
    { _rsContext :: L.Context
    , _rsBindings :: L.Bindings
    }

makeLenses ''ReplState

type ProgramStatement = Text

replEval ::
    forall m.
    (MonadState ReplState m) =>
    (ReplState -> EvalResult -> m ()) ->
    (ReplState -> Error -> m ()) ->
    ProgramStatement ->
    m ()
replEval reportResult reportError statement =
    runExceptT eval >>= report
  where
    eval :: ExceptT Error m EvalResult
    eval = parse statement >>= evaluateStatement

    report :: Either Error EvalResult -> m ()
    report res = do
        s <- use id
        either (reportError s) (reportResult s) res

emptyContext :: L.Context
emptyContext = []

initialReplState :: ReplState
initialReplState = RS emptyContext L.emptyBindings

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
testRepl program = runRWS run () initialReplState ^. (_3 . to NE.fromList)
  where
    -- fixme slow to append lists

    run = traverse (replEval saveResult saveError) program
    saveResult state res = tell . singleton $ (Right res, state)
    saveError state err = tell . singleton $ (Left err, state)

data EvalResult
    = EvAssumed (NonEmpty (Parser.Identifier, L.Value))
    | EvLet Parser.Identifier L.Type
    | EvRes L.Value (Maybe L.Type)

printEvalRes :: EvalResult -> IO ()
printEvalRes = TIO.putStrLn . showEvalRes

showEvalRes :: EvalResult -> Text
showEvalRes (EvAssumed results) = "Assumed: " <> names
  where
    names = fold $ NE.intersperse ", " ((identifier2text . (^. _1)) <$> results)
showEvalRes (EvRes val typ) = showValue val <> " :: " <> typeText
  where
    typeText = maybe "?" showValue typ
showEvalRes (EvLet name typ) = identifier2text name <> " :: " <> showValue typ

identifier2text :: Parser.Identifier -> Text
identifier2text = coerce

parse :: (MonadError Error m) => ProgramStatement -> m Parser.Statement
parse statement =
    Parser.parseStatement statement
        & either
            (throwError . ParseError)
            pure

compile :: (MonadError Error m) => Parser.Expr -> m L.Expression
compile e =
    L.compileExpr e
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
            modifying rsBindings ((coerce name, value) :)
            modifying rsContext ((L.id2id name, typ') :)
            pure $ EvLet name typ'

evalExpression :: (MonadState ReplState m, MonadError Error m) => L.Expression -> m (L.Value, (Maybe L.Type))
evalExpression (L.ExprUp e) = do
    bs <- use rsBindings
    ctx <- use rsContext
    case L.typeUp ctx bs e of
        Left err -> throwError $ TypeError err
        Right typ -> pure $ (L.evalUp bs L.emptyEnv e, Just typ)
evalExpression (L.ExprDown e) = do
    bs <- use rsBindings
    pure $ (L.evalDown bs L.emptyEnv e, Nothing)

assume :: (MonadState ReplState m, MonadError Error m) => Parser.TypeAssume -> m (Parser.Identifier, L.Type)
assume (Parser.TypeAssume n typ) = do
    compiled <- compile typ
    -- fixme incomplete pattern match
    (assumeType, _) <- evalExpression compiled
    modifying rsContext ((L.id2id n, assumeType) :) $> (n, assumeType)

type NamePool = [Text]

acquireName :: MonadState NamePool m => m Text
acquireName = gets head <* modify tail

releaseName :: MonadState NamePool m => Text -> m ()
releaseName n = modify (n :)

withName :: MonadState NamePool m => (Text -> m a) -> m a
withName f = acquireName >>= (\name -> f name <* releaseName name)

showDown :: MonadState NamePool m => NamePool -> L.TermDown -> m Text
showDown binding (L.Inf t) = showUp binding t
showDown binding (L.Lambda d) = do
    withName $ \var -> do
        body <- showDown (var : binding) d
        pure $ wrap var body
  where
    wrap var body = "λ" <> var <> " → " <> body

showUp :: MonadState NamePool m => NamePool -> L.TermUp -> m Text
showUp binding (L.Bound n) = pure (binding !! n)
showUp _ (L.Free name) = pure $ displayName name
showUp binding (L.Ann term typ) = do
    term' <- showDown binding term
    typ' <- showDown binding typ
    pure $ term' <> " :: " <> typ'
showUp binding (L.App f arg) = wrap <$> showUp binding f <*> showDown binding arg
  where
    wrap f' arg' = "(" <> f' <> " " <> arg' <> ")"
showUp _ L.Star = pure "*"
showUp _ L.Nat = pure "Nat"
showUp _ L.Zero = pure "Zero"
showUp binding (L.NatElim a b c d) = do
    a' <- showDown binding a
    b' <- showDown binding b
    c' <- showDown binding c
    d' <- showDown binding d
    pure $ "(natElim (" <> a' <> ") (" <> b' <> ") (" <> c' <> ") (" <> d' <> "))"
showUp binding (L.Succ a) = do
    prev <- showDown binding a
    pure $ "Succ (" <> prev <> ")"
showUp binding (L.Pi domain range) = do
    withName $ \var -> do
        f <- showDown (var : binding) domain
        t <- showDown (var : binding) range
        pure $ "(∀ (" <> var <> " :: " <> f <> "). " <> t <> ")"
showUp binding (L.Nil alpha) = do
    a <- showDown binding alpha
    pure $ "(Nil " <> a <> ")"
showUp binding (L.Vec alpha n) = do
    a <- showDown binding alpha
    s <- showDown binding n
    pure $ "(Vec (" <> a <> ") (" <> s <> "))"
showUp binding (L.Cons a b c d) = do
    a' <- showDown binding a
    b' <- showDown binding b
    c' <- showDown binding c
    d' <- showDown binding d
    pure $ "(Cons (" <> a' <> ") (" <> b' <> ") (" <> c' <> ") (" <> d' <> "))"
showUp binding (L.VecElim a b c d e f) = do
    a' <- showDown binding a
    b' <- showDown binding b
    c' <- showDown binding c
    d' <- showDown binding d
    e' <- showDown binding e
    f' <- showDown binding f
    pure $ "(vecElim (" <> a' <> ") (" <> b' <> ") (" <> c' <> ") (" <> d' <> ") (" <> e' <> ") (" <> f' <> "))"

showExpression :: MonadState NamePool m => NamePool -> L.Expression -> m Text
showExpression pool (L.ExprUp term) = showUp pool term
showExpression pool (L.ExprDown term) = showDown pool term

displayName :: L.Name -> Text
displayName (L.Global t) = t
displayName (L.Local _) = error "local display"
displayName (L.Quote _) = error "quote display"

showValue :: L.Value -> Text
showValue term = evalState (showDown [] (L.quote term)) nameSource

nameSource :: NamePool
nameSource = usual ++ (("a" <>) . Text.pack . show <$> [(1 :: Int) ..])
  where
    usual = ["x", "y", "z", "u", "v", "w", "r", "s", "t"]
