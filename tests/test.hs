{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Prelude hiding (exp)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

import Control.Lens hiding ((<|))
import Data.Foldable (traverse_)
import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text.Lens (packed)
import Data.Text.Strict.Lens (_Text)
import DepLambda qualified as L
import DepParser
import Repl
import Text.Megaparsec (errorBundlePretty, runParser)
import Text.Pretty.Simple (pPrint)
import qualified Data.Text as T

main = defaultMain tests

tests :: TestTree
tests =
    testGroup
        "Tests"
        $ [ boolTest
          , evenTest
          , natsTest
          , vectorTests
          , parserTests
          , evaluationTests
          , replTests
          ]

booleans :: NonEmpty ProgramStatement
booleans = [ -- "let Bool = Pi (a :: *) (first :: a) (second :: a). a"
             "let Bool = Pi (a :: *). a -> a -> a"
           , "let True = (\\_ first _ -> first) :: Bool"
           , "let False = (\\_ _ second -> second) :: Bool"
           , "let not =  (\\bool -> bool Bool False True) :: Bool -> Bool"
           , "let if = (\\a bool t f -> bool a t f) :: Pi (a :: *). Bool -> a -> a -> a"
           , "let and = (\\a -> if (Bool -> Bool) a (\\x -> x)    (\\_ -> False)) :: Bool -> Bool -> Bool"
           , "let or =  (\\a -> if (Bool -> Bool) a (\\_ -> True) (\\x -> x))     :: Bool -> Bool -> Bool"
           ]


boolTest = testGroup "booleans"
    [ -- testCase "booleans module" $  print $ testRepl booleans ^.. (folded._1._Left)
      testCase "if Nat True 1 2" $ assertReplResult (program "if Nat True 1 2") (L.Inf $ L.nat2nat 1) L.Nat
    , testCase "if Nat False 1 2" $ assertReplResult (program "if Nat False 1 2") (L.Inf $ L.nat2nat 2) L.Nat
    , testCase "if Nat (not True) 1 2" $ assertReplResult (program "if Nat (not True) 1 2") (L.Inf $ L.nat2nat 2) L.Nat
    , testCase "if Nat (and True True) 1 2" $ assertReplResult (program "if Nat (and True True) 1 2") (L.Inf $ L.nat2nat 1) L.Nat
    , testCase "if Nat (and True False) 1 2" $ assertReplResult (program "if Nat (and True False) 1 2") (L.Inf $ L.nat2nat 2) L.Nat
    , testCase "if Nat (or True False) 1 2" $ assertReplResult (program "if Nat (or True False) 1 2") (L.Inf $ L.nat2nat 1) L.Nat
    , testCase "if Nat (or False False) 1 2" $ assertReplResult (program "if Nat (or False False) 1 2") (L.Inf $ L.nat2nat 2) L.Nat
    ]
    where program exp = booleans <> [exp]


defineEven = booleans <>
    [ "let mEven = (\\_ -> Bool) :: Nat -> *"
    , "let mzeroEven = True"
    , "let msuccEven = (\\_ prev -> not prev) :: Nat -> Bool -> Bool"
    , "let even = (\\n -> natElim mEven mzeroEven msuccEven n) :: Nat -> Bool"
    ]

evenTest = testGroup "even Nats"
    [ -- testCase "even module" $  print $ testRepl defineEven ^.. (folded._1._Left)
      testCase "even 0" $ assertReplResult (program "if Nat (even 0) 0 1") (L.Inf $ L.Zero) L.Nat
    , testCase "even 3" $ assertReplResult (program "if Nat (even 3) 1 0") (L.Inf $ L.Zero) L.Nat
    , testCase "even 42" $ assertReplResult (program "if Nat (even 42) 0 1") (L.Inf $ L.Zero) L.Nat
    ]
    where program exp = defineEven <> [exp]

naturals :: NonEmpty ProgramStatement
naturals =
    [ "let foldNat = (\\alpha a f -> natElim (\\_ -> alpha) a (\\_ rec -> f rec)) :: Pi (alpha :: *). alpha -> (alpha -> alpha) -> Nat -> alpha"
    , "let caseNat = (\\alpha caseZero caseSucc -> natElim (\\_ -> alpha) caseZero (\\prev _ -> caseSucc prev)) :: Pi (a :: *). a -> (Nat -> a) -> Nat -> a"
    , "let isZero = caseNat Bool True (\\_ -> False)"
    , "let equalNat = foldNat (Nat -> Bool) isZero (\\prevEq -> caseNat Bool False (\\prev -> prevEq prev))"
    ]

natsTest = testGroup "naturals module"
    [ -- testCase "naturals module" $  print $ testRepl (booleans <> naturals) ^.. (folded._1._Left)
      testCase "if Nat (isZero 0) 0 1" $ assertReplResult (program "if Nat (isZero 0) 0 1") (L.Inf L.Zero) L.Nat
    , testCase "if Nat (isZero 5) 1 0" $ assertReplResult (program "if Nat (isZero 5) 1 0") (L.Inf L.Zero) L.Nat
    , testCase "foldNat Nat 0 Succ 5"  $ assertReplResult (program "foldNat Nat 0 Succ 5") (L.Inf $ L.nat2nat 5) L.Nat
    , testCase "if Nat (equalNat 4 4) 0 1"  $ assertReplResult (program "if Nat (equalNat 4 4) 0 1") (L.Inf $ L.Zero) L.Nat
    , testCase "if Nat (equalNat 3 4) 1 0"  $ assertReplResult (program "if Nat (equalNat 3 4) 1 0") (L.Inf $ L.Zero) L.Nat
    ]
    where program exp = booleans <> naturals <> [exp]


vectors :: NonEmpty ProgramStatement
vectors =
    [ "let _mapM = (\\a b k _ -> ((a -> b) -> Vec b k)) :: Pi (a :: *) (b :: *) (k :: Nat). Vec a k -> *"
    , "let _mapMZero = (\\a b _ -> Nil b) :: Pi (a :: *) (b :: *). (a -> b) -> Vec b 0"
    , "let _mapMCons = (\\a b k head tail rec f -> Cons b k (f head) (rec f)) :: Pi (a :: *) (b :: *) (k :: Nat) (head :: a) (tail :: Vec a k). ((a -> b) -> Vec b k) -> (a -> b) -> Vec b (Succ k)"
    , "let map = (\\a b -> vecElim a (_mapM a b) (_mapMZero a b) (_mapMCons a b)) :: Pi (a :: *) (b :: *) (k :: Nat). Vec a k -> (a -> b) -> Vec b k"
    , "let _caseVecM = (\\a b k vec -> b) :: Pi (a :: *) (b :: *) (k :: Nat). Vec a k -> *"
    , "let _caseVecMCons = (\\a b caseCons k head tail rec -> caseCons a k head tail) :: Pi (a :: *) (b :: *) (caseCons :: Pi (a :: *) (k :: Nat). a -> Vec a k -> b) (k :: Nat). a -> Vec a k -> b -> b"
    , "let caseVec = (\\a b caseNil caseCons -> vecElim a (_caseVecM a b) caseNil (_caseVecMCons a b caseCons)) :: Pi (a :: *) (b :: *) (caseNil :: b) (caseCons :: Pi (a :: *) (k :: Nat). a -> Vec a k -> b) (k :: Nat). Vec a k -> b"
    , "let null = (\\a -> caseVec a Bool True (\\_ _ _ _ -> False)) :: Pi (a ::*) (k :: Nat) (v :: Vec a k). Bool"

    ]

vectorTests = testGroup "vectors tests"
    [ -- testCase "vectors module" $  print $ testRepl (booleans <> vectors) ^.. (folded._1._Left)
      testCase "map Nat Nat 0 (Nil Nat) Succ" $ assertReplResult (program "map Nat Nat 0 (Nil Nat) Succ") (L.Inf (L.Nil $ L.Inf L.Nat)) (L.Vec (L.Inf L.Nat) (L.Inf L.Zero))
    , testCase "map Nat Nat 1 (Cons Nat 0 5 (Nil Nat)) Succ" $ assertReplResult (program "map Nat Nat 1 (Cons Nat 0 5 (Nil Nat)) Succ") (L.Inf (L.Cons (L.Inf L.Nat) (L.Inf L.Zero) (L.Inf $ L.nat2nat 6) (L.Inf (L.Nil (L.Inf L.Nat)))))  (L.Vec (L.Inf L.Nat) (L.Inf $ L.nat2nat 1))
    , testCase "map Bool Nat 1 (Cons Nat 0 5 (Nil Nat)) Succ" $ assertReplResult (program "map Nat Nat 1 (Cons Nat 0 5 (Nil Nat)) Succ") (L.Inf (L.Cons (L.Inf L.Nat) (L.Inf L.Zero) (L.Inf $ L.nat2nat 6) (L.Inf (L.Nil (L.Inf L.Nat)))))  (L.Vec (L.Inf L.Nat) (L.Inf $ L.nat2nat 1))
    , testCase "if Nat (null Nat 0 (Nil Nat)) 0 1" $ assertReplResult (program "if Nat (null Nat 0 (Nil Nat)) 0 1") (L.Inf L.Zero) L.Nat 
    , testCase "if Nat (null Nat 1 (Cons Nat 0 5 (Nil Nat))) 1 0" $ assertReplResult (program "if Nat (null Nat 0 (Nil Nat)) 0 1") (L.Inf L.Zero) L.Nat 
    

    ]
    where program exp = booleans <> defineEven <> vectors <> [exp]

assertParse :: HasCallStack => ProgramStatement -> Statement -> Assertion
assertParse s res = do
    case parseStatement s of
        Left e -> assertFailure (errorBundlePretty e)
        Right a -> res @=? a

shorten n t = if T.length t > n then T.take (n - 3) t `T.append` "..." else t

parserCase :: ProgramStatement -> Statement -> TestTree
parserCase s res = testCase (packed # shorten 60 s) $ assertParse s res

parserTests =
    testGroup
        "Parser tests"
        [ parserCase "Nat" $ StExpr (Var "Nat")
        , parserCase "  Nat " $ StExpr (Var "Nat")
        , parserCase "5" $ StExpr (LiteralNat 5)
        , parserCase "Zero" $ StExpr (Var "Zero")
        , parserCase "5 :: Nat" $ StExpr (Ann (LiteralNat 5) (Var "Nat"))
        , parserCase "(5)" $ StExpr (LiteralNat 5)
        , parserCase " ( 5 :: Nat )  " $ StExpr (Ann (LiteralNat 5) (Var "Nat"))
        , parserCase "Succ (Succ 5)" $ StExpr (App (Var "Succ") (App (Var "Succ") (LiteralNat 5)))
        , parserCase "Vec Nat 5" $ StExpr (App (App (Var "Vec") (Var "Nat")) (LiteralNat 5))
        , parserCase "Cons Nat 5 40 xs" $ StExpr (App (App (App (App (Var "Cons") (Var "Nat")) (LiteralNat 5)) (LiteralNat 40)) (Var "xs"))
        , parserCase "Nat -> Nat" $ StExpr (Function (Var "Nat") (Var "Nat"))
        , parserCase " ((λx -> x):: alpha -> alpha ) a " $
            StExpr $
                App
                    ( Ann
                        (Lambda (Identifier "x" :| []) (Var (Identifier "x")))
                        (Function (Var (Identifier "alpha")) (Var (Identifier "alpha")))
                    )
                    (Var (Identifier "a"))
        , parserCase "let x = 1 :: Nat" $ StLet "x" (Ann (LiteralNat 1) (Var "Nat"))
        , parserCase "assume x :: Nat" $ StAssume [TypeAssume "x" (Var "Nat")]
        , parserCase "assume (x :: Nat)  (y :: *)" $ StAssume [TypeAssume "x" (Var "Nat"), TypeAssume "y" Star]
        , parserCase "let plus = natElim (λ_ → Nat → Nat) (λn → n) (λk rec n → Succ (rec n))" $
            StLet "plus" $
                ( App
                    ( App
                        ( App
                            (Var "natElim")
                            (Lambda ["_"] (Function (Var "Nat") (Var "Nat")))
                        )
                        (Lambda ["n"] (Var "n"))
                    )
                    (Lambda ["k", "rec", "n"] (App (Var "Succ") (App (Var "rec") (Var "n"))))
                )
        , parserCase "(λα → vecElim α (λm _ → ∀(n :: Nat).Vec α n → Vec α (plus m n)) (λ _ v → v) (λm v vs rec n w → Cons α (plus m n) v (rec n w))) :: ∀(α :: ∗) (m :: Nat) (v :: Vec α m) (n :: Nat) (w :: Vec α n). Vec α (plus m n)" $
            StExpr $ 
            Ann (Lambda (Identifier "\945" :| [])
                        (App
                            (App
                                (App
                                    (App (Var (Identifier "vecElim")) (Var (Identifier "\945")))
                                    (Lambda (Identifier "m" :| [Identifier "_"]) (Pi ((Identifier "n",Var (Identifier "Nat")) :| []) (Function (App (App (Var (Identifier "Vec")) (Var (Identifier "\945"))) (Var (Identifier "n"))) (App (App (Var (Identifier "Vec")) (Var (Identifier "\945"))) (App (App (Var (Identifier "plus")) (Var (Identifier "m"))) (Var (Identifier "n"))))))))
                                (Lambda (Identifier "_" :| [Identifier "v"]) (Var (Identifier "v"))))
                            (Lambda (Identifier "m" :| [Identifier "v",Identifier "vs",Identifier "rec",Identifier "n",Identifier "w"]) (App (App (App (App (Var (Identifier "Cons")) (Var (Identifier "\945"))) (App (App (Var (Identifier "plus")) (Var (Identifier "m"))) (Var (Identifier "n")))) (Var (Identifier "v"))) (App (App (Var (Identifier "rec")) (Var (Identifier "n"))) (Var (Identifier "w")))))))
                (Pi ((Identifier "\945",Star) :| [(Identifier "m",Var (Identifier "Nat")),(Identifier "v",App (App (Var (Identifier "Vec")) (Var (Identifier "\945"))) (Var (Identifier "m"))),(Identifier "n",Var (Identifier "Nat")),(Identifier "w",App (App (Var (Identifier "Vec")) (Var (Identifier "\945"))) (Var (Identifier "n")))]) (App (App (Var (Identifier "Vec")) (Var (Identifier "\945"))) (App (App (Var (Identifier "plus")) (Var (Identifier "m"))) (Var (Identifier "n")))))
        ]

assertEval :: HasCallStack => ProgramStatement -> L.TermUp -> Assertion
assertEval s expected = 
    let Right (StExpr parsed) = parseStatement s
        Right (L.ExprUp compiled) = L.compileExpr parsed
        res = L.evalUp L.emptyBindings L.emptyEnv compiled
    in L.quote res @?= L.Inf expected 


evalCase :: ProgramStatement -> L.TermUp -> TestTree
evalCase s res = testCase (packed # s) $ assertEval s res

evaluationTests =
    testGroup
        "Evaluation tests"
        [ evalCase "Succ Zero" (L.nat2nat 1)
        , evalCase "((λ x → Succ x) :: Nat → Nat) Zero" (L.nat2nat 1)
        , evalCase "((λ x → Succ (Succ x)) :: Nat → Nat) Zero" (L.nat2nat 2)
        , testCase "plus 2 1 == 3" $ assertEval "(natElim (λ x → Nat → Nat) (λ n → n) (λ k rec n → Succ (rec n))) 2 1" (L.nat2nat 3)
        , evalCase "Vec Nat 1" (L.Vec (L.Inf L.Nat) (L.Inf $ L.Succ (L.Inf L.Zero)))
        , evalCase "Nil Nat" (L.Nil $ L.Inf L.Nat)
        , evalCase "Cons Nat 0 1 (Nil Nat)" (L.Cons (L.Inf L.Nat) (L.Inf L.Zero) (L.Inf $ L.Succ $ L.Inf L.Zero) (L.Inf $ L.Nil $ L.Inf L.Nat))
        
        ]

assertReplResult :: HasCallStack => NonEmpty ProgramStatement -> L.TermDown -> L.TermUp -> Assertion
assertReplResult program value typ =
    case res of
        Just (Right (EvRes value' (Just typ'))) -> do
            value @=? L.quote value'
            L.Inf typ @=? L.quote typ'
        Just (Right other) -> assertFailure $ "Repl result invalid: " <> (from _Text # showEvalRes other)
        Just (Left err) -> assertFailure $ "Unexpected repl error: " <> show err
        other -> assertFailure "No repl result"
  where
    res = lastOf (folded . _1) $ testRepl program


replTests =
    testGroup
        "REPL tests"
        [ testCase "Succ 0" $  assertReplResult ["Succ 0"] (L.Inf $ L.Succ $ L.Inf L.Zero) L.Nat
        , testCase "Succ 0; ((\\x -> Succ x) :: Nat -> Nat) 0" $  assertReplResult ["Succ 0", "((\\x -> Succ x) :: Nat -> Nat) 0"] (L.Inf $ L.Succ $ L.Inf L.Zero) L.Nat
        , testCase "let a = 1; Succ a" $  assertReplResult ["let a = 1", "Succ a"] (L.Inf $ L.Succ $ L.Inf $ L.Succ $ L.Inf L.Zero) L.Nat
        , testCase "succ a" $ assertReplResult ["assume (x :: Nat)", "Succ x"] (L.Inf $ L.Succ (L.Inf $ (L.Free $ L.Global "x"))) L.Nat
        , testCase "assume a + id a" $ assertReplResult
                [ "assume (alpha :: *) (beta :: *)"
                , "assume (a :: alpha) (b :: beta)"
                , "((λx -> x) :: alpha -> alpha) a"
                ]
                (L.Inf $ L.Free $ L.Global "a")
                (L.Free $ L.Global "alpha")

        , testCase "plus 40 2" $
            assertReplResult
                [ "let plus = natElim (λ_ → Nat → Nat) (λn → n) (λk rec n → Succ (rec n))"
                , "plus 40 2"
                ]
                (L.Inf $ L.nat2nat 42)
                (L.Nat)

        , testCase "append" $
            let alpha = L.Inf (L.Free (L.Global "α"))
                x = L.Inf (L.Free (L.Global "x"))
                y = L.Inf (L.Free (L.Global "y"))
            in assertReplResult
                   [ "let plus = natElim (λ _ → Nat → Nat) (λn → n) (λk rec n → Succ (rec n))"
                   , "let append = (λα → vecElim α (λm _ → ∀(n :: Nat).Vec α n → Vec α (plus m n)) (λ _ v → v) (λm v vs rec n w → Cons α (plus m n) v (rec n w))) :: ∀(α :: ∗) (m :: Nat) (v :: Vec α m) (n :: Nat) (w :: Vec α n). Vec α (plus m n)"
                   , "assume (α :: ∗) (x :: α) (y :: α)"
                   , "append α 2 (Cons α 1 x (Cons α 0 x (Nil α))) 1 (Cons α 0 y (Nil α))"
                   ]
                   (L.Inf (L.Cons alpha (L.Inf $ L.nat2nat 2) x 
                                  (L.Inf (L.Cons alpha (L.Inf $ L.nat2nat 1) x (L.Inf (L.Cons alpha (L.Inf L.Zero) y (L.Inf (L.Nil alpha))))))))
                   (L.Vec alpha (L.Inf $ L.nat2nat 3))
        ]
