module Hlox
    ( interpretString
    ) where
import Analyse
import           AST
import           Control.Monad                  ( foldM
                                                , void
                                                )
import qualified Control.Monad.Except          as Ex
import qualified Control.Monad.State           as St
import           Data.List                      ( partition )
import           Eval
import           Lexer                          ( AToken
                                                , scanWholeString
                                                )
import           Parser                         ( ParseResult(..)
                                                , extractOutput
                                                )
import           System.Environment             ( getArgs )
import           System.IO                      ( hPutStrLn
                                                , stderr
                                                )
import           Util

interpretString :: String -> IO ()
interpretString code = runIfOk $ stringToStatements code
  where
    runIfOk (Right stmts) = execStatements stmts
    runIfOk (Left  errs ) = hPutStrLn stderr $ unlines errs

stringToStatements :: String -> Either [String] [Statement]
stringToStatements s = do
    tokens <- stringToTokens s
    stmts <- tokensToStatements tokens
    analyseStatements stmts

stringToTokens :: String -> Either [String] [AToken]
stringToTokens s = toEither $ scanWholeString s

tokensToStatements :: [AToken] -> Either [String] [Statement]
tokensToStatements ts = toEither $ extractOutput $ parseStatements ts

execStatements :: [Statement] -> IO ()
execStatements stmts = do
    res <- runCompute cleanState $ execMany stmts
    printError res  where
    printError (Left (RuntimeError s)) = hPutStrLn stderr s
    printError (Left (Return _)) =
        error "unexpected return (should've been caught during static analysis)"
    printError (Right ()) = return ()
