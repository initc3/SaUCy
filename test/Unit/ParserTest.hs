module Unit.ParserTest (
    test_parser
  ) where

import Text.Printf
import Test.Tasty
import Test.Tasty.HUnit

import Language.ILC.Decl
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
      , Right [ Decl "it" (ENu ("c", "c'") (EWr (ELit $ LInt 1)
                                       (EVar "c")))
              ]
      )
    , ( "let binding w/ tuple matching"
      , "let (x, y) = (1, 2) in x + y"
      , Right [ Decl "it" (ELet (PTuple [PVar "x", PVar "y"])
                            (ETuple [ELit $ LInt 1, ELit $ LInt 2])
                            (EBin Add (EVar "x")
                                           (EVar "y")))
              ]
      )
    , ( "let binding w/ unit and function application"
      , "let () = \"whatever\" in double 2"
      , Right [ Decl "it" (ELet PUnit
                            (ELit $ LString "whatever")
                            (EApp (EVar "double")
                                  (ELit $ LInt 2)))
              ]
      )
    , ( "nested let bindings"
      , "let x = 1 in let y = 2 in x + y"
      , Right [ Decl "it" (ELet (PVar "x")
                            (ELit $ LInt 1)
                            (ELet (PVar "y")
                                  (ELit $ LInt 2)
                                  (EBin Add (EVar "x")
                                                 (EVar "y"))))
              ]
      )
    , ( "let commands"
      , "let x = 1 let y = 2 let z = x + y"
      , Right [ Decl "x" (ELit $ LInt 1)
              , Decl "y" (ELit $ LInt 2)
              , Decl "z" (EBin Add (EVar "x")
                                    (EVar "y"))
              ]
      )
    , ( "pattern matching"
      , "match b with | 0 => \"zero\" | 1 => \"one\""
      , Right [ Decl "it" (EMatch (EVar "b")
                              [ (PInt 0
                                , ELit $ LBool True
                                , ELit $ LString "zero")
                              , (PInt 1
                                , ELit $ LBool True
                                , ELit $ LString "one")
                              ])
              ]
      )
    , ( "cons pattern matching"
      , "match a with | [] => 0 | x:xs => 1"
      , Right [ Decl "it" (EMatch (EVar "a")
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
      , Right [ Decl "it" (EMatch (EVar "b")
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
