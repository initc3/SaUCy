module Unit.ParserTest (
    test_parser
  ) where

import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Language.ILC.Eval
import Language.ILC.Parser
import Language.ILC.Syntax

test_parser :: TestTree
test_parser =
    testGroup "Unit.ParserTest" $ map f examples
  where f (str, src, ast) = testCase (printf "Parse %s" str) $
                            assertEqual "" (parser src) ast
                           
examples =
    [ ( "allocate channel then write"
      , "nu c . wr 1 -> c"
      , Right [ ("it", ENu ("c", "c'") (EWr (ELit $ LInt 1)
                                       (EVar "c")))
              ]
      )
    , ( "let binding w/ tuple matching"
      , "let (x, y) = (1, 2) in x + y"
      , Right [ ("it", ELet (PTuple [PVar "x", PVar "y"])
                            (ETuple [ELit $ LInt 1, ELit $ LInt 2])
                            (EBin Add (EVar "x")
                                           (EVar "y")))
              ]
      )
    , ( "let binding w/ unit and function application"
      , "let () = \"whatever\" in double 2"
      , Right [ ("it", ELet PUnit
                            (ELit $ LString "whatever")
                            (EApp (EVar "double")
                                  (ELit $ LInt 2)))
              ]
      )
    , ( "sequencing let bindings"
      , "let x = 1 in x; let y = 1 in y"
      , Right [ ("it", ELet (PVar "x")
                            (ELit $ LInt 1)
                            (ESeq (EVar "x")
                                  (ELet (PVar "y")
                                        (ELit $ LInt 1)
                                        (EVar "y"))))
              ]
      )
    , ( "nested let bindings"
      , "let x = 1 in let y = 2 in x + y"
      , Right [ ("it", ELet (PVar "x")
                            (ELit $ LInt 1)
                            (ELet (PVar "y")
                                  (ELit $ LInt 2)
                                  (EBin Add (EVar "x")
                                                 (EVar "y"))))
              ]
      )
    , ( "let commands"
      , "let x = 1 let y = 2 let z = x + y"
      , Right [ ("x", ELit $ LInt 1)
              , ("y", ELit $ LInt 2)
              , ("z", EBin Add (EVar "x")
                                    (EVar "y"))
              ]
      )
    , ( "let command, let binding, expr command"
      , "let z = let x = 1 in 2 * x let y = 1;; \"foo\""
      , Right [ ("z", ELet (PVar "x")
                           (ELit $ LInt 1)
                           (EBin Mul (ELit $ LInt 2)
                                          (EVar "x")))
              , ("y", ELit $ LInt 1)
              , ("it", ELit $ LString "foo")
              ]
      )
    , ( "expr commands and sequencing"
      , "1 ; 2 ;; 3 ; 4"
      , Right [ ("it", ESeq (ELit $ LInt 1)
                            (ELit $ LInt 2))
              , ("it", ESeq (ELit $ LInt 3)
                            (ELit $ LInt 4))
              ]
      )
    , ( "pattern matching"
      , "match b with | 0 => \"zero\" | 1 => \"one\""
      , Right [ ("it", EMatch (EVar "b")
                              [ (PInt 0
                                , ELit $ LBool True
                                , ELit $ LString "zero")
                              , (PInt 1
                                , ELit $ LBool True
                                , ELit $ LString "one")
                              ])
              ]
      )
    , ( "let binding w/ assign"
      , "let x = 1 ; let y := 1 in x + y"
      , Right [ ("it", ELet (PVar "x")
                            (ESeq (ELit $ LInt 1)
                                  (ESet "y"
                                           (ELit $ LInt 1)))
                            (EBin Add (EVar "x")
                                           (EVar "y")))
              ]
      )
    , ( "ref and deref"
      , "let a = ref 1 ;; let b := @ a"
      , Right [ ("a", ERef (ELit $ LInt 1))
              , ("it", ESet "b"
                               (EGet (EVar "a")))
              ]
      )
    , ( "let binding w/ sequencing and assign"
      , "let a = 1 ; let b := 1 in b"
      , Right [ ("it", ELet (PVar "a")
                            (ESeq (ELit $ LInt 1)
                                  (ESet "b"
                                           (ELit $ LInt 1)))
                            (EVar "b"))
              ]
      )
    , ( "cons pattern matching"
      , "match a with | [] => 0 | x:xs => 1"
      , Right [ ("it", EMatch (EVar "a")
                              [ ( PList []
                                , ELit $ LBool True
                                , ELit $ LInt 0)
                              , ( PCons (PVar "x")
                                        (PVar "xs")
                                , ELit $ LBool True
                                , ELit $ LInt 1)
                              ])
              ]
      )
    , ( "pattern matching with guards"
      , "match b with | 0 when 0 < 1 => 0 | 1 when true => 1"
      , Right [ ("it", EMatch (EVar "b")
                               [ ( PInt 0
                                 , EBin Lt (ELit $ LInt 0)
                                              (ELit $ LInt 1)
                                 , ELit $ LInt 0)
                               , ( PInt 1
                                 , ELit $ LBool True
                                 , ELit $ LInt 1)
                               ])
              ]
      )
    ]
