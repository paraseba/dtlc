{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module DepParser where

import Prelude hiding (succ, pi, exp)

import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Text (Text)
import Data.Void
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import Data.Functor (void, ($>))
import Data.String (IsString)
import qualified Data.List.NonEmpty as NE
import Data.Foldable (asum)
import Numeric.Natural (Natural)
import Text.Megaparsec.Char.Lexer (decimal)
import Control.Monad.Combinators.Expr (makeExprParser, Operator (..))

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

data Expr =
    Pi (NE.NonEmpty (Identifier, Expr)) Expr
    | LiteralNat Natural
    | Function Expr Expr
    | Lambda (NE.NonEmpty Identifier) Expr
    | Var Identifier
    | App Expr Expr
    | Ann Expr Expr
    | Star
    deriving (Eq, Show)


data TypeAssume = TypeAssume Identifier Expr
    deriving (Eq, Show)

data Statement =
    StAssume (NE.NonEmpty TypeAssume)
    | StLet Identifier Expr
    | StExpr Expr
    deriving (Eq, Show)


symbols :: [Text] -> Parser Text
symbols = asum . map symbol

syntax :: [Text] -> Parser ()
syntax = void . symbols

piSym :: Parser ()
piSym = syntax ["Pi", "forall", "Π", "∀"] <?> "Pi"

arrowSym :: Parser ()
arrowSym = syntax ["->", "→"] <?> "->"

lambdaSym :: Parser ()
lambdaSym = syntax ["\\", "λ"] <?> "\\"

assumeSym :: Parser ()
assumeSym = syntax ["assume"]

ofTypeSym :: Parser ()
ofTypeSym = syntax ["::"]

starSym :: Parser ()
starSym = syntax ["∗", "*", "Type"]

lineEnd :: Parser ()
lineEnd  = void eol <|> eof

assumeParser :: Parser Statement
assumeParser = StAssume <$> (assumeSym *>  parser)
  where
    parser =
        NE.singleton <$> try typeAssumeParser
        <|> NE.some1 (parens typeAssumeParser)

statementParser :: Parser Statement
statementParser = sc *> (assumeParser <|> letParser <|> StExpr <$> expression) <* eof

letParser :: Parser Statement
letParser =
    StLet
    <$> (sc *> symbol "let" *> identifierParser)
    <*> (symbol "=" *> expression)

identifierParser :: Parser Identifier
identifierParser =
    Identifier . T.pack <$> lexeme name
        where name = (:) <$> (letterChar <|> char '_') <*> many alphaNumChar <?> "identifier"


typeAssumeParser :: Parser TypeAssume
typeAssumeParser = TypeAssume <$> (identifierParser <* ofTypeSym) <*> exp



literalNat :: Parser Expr
literalNat = LiteralNat <$> lexeme decimal


lambdaParser :: Parser Expr
lambdaParser = do
    lambdaSym
    args <- NE.some1 identifierParser
    arrowSym
    Lambda args <$> exp
   
pi :: Parser Expr
pi = do
    piSym
    args <- argsParser
    syntax ["."]
    expr <- exp
    pure $ Pi args expr
    where
        argsParser = NE.some1 (parens argParser) --fixme allow single arguments without parens
        argParser = do
            ident <- try identifierParser
            try ofTypeSym
            typ <- exp
            pure (ident, typ)


expression :: Parser Expr
expression = sc *> exp

exp :: Parser Expr
exp = makeExprParser term table

term :: Parser Expr
term = parens exp
       <|> (starSym $> Star)
       <|> literalNat
       <|> pi
       <|> lambdaParser
       <|> Var <$> try identifierParser

table :: [[Operator Parser Expr]]
table = [ [InfixL $ pure App]
        , [InfixR $ Function <$ arrowSym]
        , [InfixL $ Ann <$ ofTypeSym ]
        ]

parseStatement :: Text -> Either (ParseErrorBundle Text Void) Statement
parseStatement statement =
    runParser statementParser "input" statement



