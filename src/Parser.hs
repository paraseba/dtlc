{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Parser where

import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Text (Text)
import Data.Void
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import Data.Functor (void)
import Data.String (IsString)
import qualified Data.List.NonEmpty as NE

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

newtype Identifier = Identifier Text
    deriving (Eq, Show, IsString)

data Type =
    TId Identifier
    | TFun Type Type
    deriving (Show)

data AssumeItem =
    TypeAssume Identifier Type
    | KindAssume Identifier
    deriving (Show)

data Statement =
    StAssume (NE.NonEmpty AssumeItem)
    | StExpr Expr
    deriving (Show)


lineEnd :: Parser ()
lineEnd  = void eol <|> eof

assumeParser :: Parser Statement
assumeParser = StAssume <$> (symbol "assume" *>  parser)
  where
    parser =
        NE.singleton <$> kindOrType
        <|> NE.some1 (parens kindOrType)
    kindOrType = try kindAssumeParser <|> try typeAssumeParser

statementParser :: Parser Statement
statementParser = sc *> (assumeParser <|> StExpr <$> exprParser) <* eof

identifierParser :: Parser Identifier
identifierParser =
    Identifier . T.pack <$> lexeme name
        where name = (:) <$> letterChar <*> many alphaNumChar <?> "identifier"

kindAssumeParser :: Parser AssumeItem
kindAssumeParser = KindAssume <$> identifierParser <* symbol "::" <* symbol "*"

typeAssumeParser :: Parser AssumeItem
typeAssumeParser = TypeAssume <$> (identifierParser <* symbol "::") <*> typeParser


typeParser :: Parser Type
typeParser = do
    s <- start
    e <- end
    case e of
      Just to -> pure $ TFun s to
      Nothing -> pure s
    where
      start = parens typeParser
              <|> TId <$> identifierParser
      end = optional ( (symbol "->" <|> symbol "→") *> typeParser)



data Expr =
    Lambda (NE.NonEmpty Identifier) Expr
    | Var Identifier
    | App Expr (NE.NonEmpty Expr)
    | Ann Expr Type
    deriving (Show)

exprParser :: Parser Expr
exprParser = do
    s <- start
    t <- optional ( symbol "::" *> typeParser)
    case t of
        Just typ -> pure $ Ann s typ
        Nothing -> do
            e <- many start
            case e of
                [] -> pure s
                (x:xs) -> pure $ App s (x NE.:| xs)
    where
      start = parens exprParser
        <|> lambdaParser
        <|> Var <$> try identifierParser


lambdaParser :: Parser Expr
lambdaParser = do
    _ <- (symbol "\\" <|> symbol "λ")
    args <- NE.some1 identifierParser
    _ <- symbol "->" <|> symbol "→"
    expr <- exprParser
    pure $ Lambda args expr


