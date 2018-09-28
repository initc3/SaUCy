{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
--{-# OPTIONS_GHC -Wall             #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Language.ILC.Repl
-- Copyright   :  (C) 2018 Kevin Liao
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Kevin Liao (kliao6@illinois.edu)
-- Stability   :  experimental
--
-- REPL for ILC.
--
--------------------------------------------------------------------------------

module Language.ILC.Repl (
      main
    ) where

import Control.Monad.State.Strict
import Data.List (isPrefixOf)
import qualified Data.Map as Map
import Data.Monoid
import Options.Applicative
import System.Console.Repline hiding (Options)
import System.Exit
import System.IO.Silently (silence)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.ILC.Decl
import Language.ILC.Eval
import Language.ILC.Infer
import Language.ILC.Parser
import Language.ILC.Syntax
import Language.ILC.Type
import Language.ILC.Value

--------------------------------------------------------------------------------
-- Command line parser
--------------------------------------------------------------------------------

data Options = Options
    { optSrcFile :: Maybe FilePath
    , optAst     :: Bool
    }

inputFile :: Parser (Maybe FilePath)
inputFile = optional $ argument str
    (  metavar "FILENAME"
    <> help "Source file" )

ast :: Parser Bool
ast = switch
    (  long "ast"
    <> help "Print abstract syntax tree" )

optParser :: Parser Options
optParser = Options <$> inputFile <*> ast

opts :: ParserInfo Options
opts = info (optParser <**> helper)
    ( fullDesc
    <> progDesc "Interactive Lambda Calculus (ILC) interpreter"
    <> header "ILC" )

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

data IState = IState
    { tyenv :: TypeEnv
    , tmenv :: TermEnv
    }

initState :: IState
initState = IState emptyTyEnv emptyTmEnv

type Repl a = HaskelineT (StateT IState IO) a
hoistErr :: Show e => Either e a -> Repl a
hoistErr (Right val) = return val
hoistErr (Left err) = do
    liftIO $ print err
    abort

--------------------------------------------------------------------------------
-- Execution
--------------------------------------------------------------------------------

-- TODO: Blocks on rd c if not function
evalDecl :: TermEnv -> Decl -> IO TermEnv
evalDecl env (x, expr) = silence $ eval env expr >>= return . extendTmEnv env x
    
execi :: Bool -> String -> Repl ()
execi update source = do
    st <- get
    
    mod <- hoistErr $ parser source
    
    tyenv' <- hoistErr $ inferTop (tyenv st) mod

    tmenv' <- liftIO $ foldM (evalDecl) (tmenv st) mod
    
    let st' = st { tmenv = tmenv'
                 , tyenv = tyenv' <> (tyenv st)
                 }

    when update (put st')
    
    case lookup "it" mod of
        Nothing -> return ()
        Just ex -> do
            val <- liftIO $ eval (tmenv st') ex
            showOutput (show $ pretty val) st'

showOutput :: String -> IState -> Repl ()
showOutput arg st = do
    case lookupTyEnv "it" (tyenv st) of
        Just val -> liftIO $ putDoc (prettySignature (arg, val) <> linebreak)
        Nothing -> return ()
    
cmd :: String -> Repl ()
cmd source = execi True source

process :: String -> IO ()
process src = do
    let cmds = parser src
    case cmds of
        Left err -> print err
        Right cmds -> Language.ILC.Eval.exec cmds >>= putDoc . pretty

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- :browse command
browse :: [String] -> Repl ()
browse _ = do
    st <- get
    liftIO $ mapM_ putStrLn $ prettyTyEnv (tyenv st)

-- :load command
load :: [String] -> Repl ()
load args = do
    contents <- liftIO $ readFile (unwords args)
    execi True contents

-- :type command
typeof :: [String] -> Repl ()
typeof args = do
    st <- get
    let arg = unwords args
    case lookupTyEnv arg (tyenv st) of
        Just val -> liftIO $ putDoc $ prettySignature (arg, val) <> linebreak
        Nothing -> execi False arg

-- :quit command
quit :: a -> Repl ()
quit _ = liftIO $ exitSuccess

-------------------------------------------------------------------------------
-- Interactive Shell
-------------------------------------------------------------------------------

-- Prefix tab completer
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher = [(":load"  , fileCompleter)]

-- Default tab completer
comp :: (Monad m, MonadState IState m) => WordCompleter m
comp n = do
    let cmds = [":load", ":type", ":browse", ":quit"]
    TypeEnv ctx <- gets tyenv
    let defs = Map.keys ctx
    return $ filter (isPrefixOf n) (cmds ++ defs)

options :: [(String, [String] -> Repl ())]
options =
    [ ("load"   , load)
    , ("browse" , browse)
    , ("quit"   , quit)
    , ("type"   , typeof)
    ]

completer :: CompleterStyle (StateT IState IO)
completer = Prefix (wordCompleter comp) defaultMatcher

shell :: Repl a -> IO ()
shell pre = flip evalStateT initState 
    $ evalRepl "λ: " cmd options Language.ILC.Repl.completer pre

main :: IO ()
main = do
    options <- execParser opts
    case (optSrcFile options) of
        Just file -> readFile file >>= process
        Nothing   -> shell (return ())
