module Lexer
    ( Token(..)
    , AToken(..)
    , scanWholeString
    ) where

import           Control.Applicative            ( Alternative(..) )
import           Data.Foldable                  ( asum )
import           Data.List                      ( isPrefixOf )
import           Parser
import           Text.Read                      ( readMaybe )
import           Util

data Token
    -- Single-character tokens
    = TLeftParen
    | TRightParen
    | TLeftBrace
    | TRightBrace
    | TComma
    | TDot
    | TMinus
    | TPlus
    | TSemicolon
    | TSlash
    | TStar
    | TBang
    | TBangEqual
    | TEqual
    | TEqualEqual
    | TGreater
    | TGreaterEqual
    | TLess
    | TLessEqual
    -- Actually interesting stuff
    | TIdentifier String
    | TString String
    | TNumber Double
    -- Keywords
    | TAnd
    | TClass
    | TElse
    | TFalse
    | TFun
    | TFor
    | TIf
    | TNil
    | TOr
    | TPrint
    | TReturn
    | TSuper
    | TThis
    | TTrue
    | TVar
    | TWhile
    -- EOF
    | TEof
    -- the lexer is simple enough that this is all we need for error handling
    | TError String
    -- some more internal tokens to make things simpler
    | TComment
    | TNewline
    | TWhitespace
    deriving (Eq, Show)

-- assuming we don't prettyprint much, 
-- this should be more effficient (and easier) than saving the lexeme
-- (only issue being that numbers get converted to floats - oh well)
instance PrettyPrint Token where
    prettyPrint TLeftParen      = "("
    prettyPrint TRightParen     = ")"
    prettyPrint TLeftBrace      = "{"
    prettyPrint TRightBrace     = "}"
    prettyPrint TComma          = ","
    prettyPrint TDot            = "."
    prettyPrint TMinus          = "-"
    prettyPrint TPlus           = "+"
    prettyPrint TSemicolon      = ";"
    prettyPrint TSlash          = "/"
    prettyPrint TStar           = "*"
    prettyPrint TBang           = "!"
    prettyPrint TBangEqual      = "!="
    prettyPrint TEqual          = "="
    prettyPrint TEqualEqual     = "=="
    prettyPrint TGreater        = ">"
    prettyPrint TGreaterEqual   = ">="
    prettyPrint TLess           = "<"
    prettyPrint TLessEqual      = "<="
    prettyPrint (TIdentifier s) = s
    prettyPrint (TString     s) = show s
    prettyPrint (TNumber     n) = show n
    prettyPrint TAnd            = "and"
    prettyPrint TClass          = "class"
    prettyPrint TElse           = "else"
    prettyPrint TFalse          = "false"
    prettyPrint TFor            = "for"
    prettyPrint TFun            = "fun"
    prettyPrint TIf             = "if"
    prettyPrint TNil            = "nil"
    prettyPrint TOr             = "or"
    prettyPrint TPrint          = "print"
    prettyPrint TReturn         = "return"
    prettyPrint TSuper          = "super"
    prettyPrint TTrue           = "true"
    prettyPrint TVar            = "var"
    prettyPrint TWhile          = "while"
    prettyPrint TEof            = error "TEof should be handled separately"
    prettyPrint _ =
        error
            "You are trying to prettyprint a debug symbol, which should never make it out of the scanner?"

-- allows for more helpful error reporting later
data AToken = AToken
    { getTokenLine   :: Int
    , getActualToken :: Token
    }
    deriving (Eq, Show)

instance PrettyPrint AToken where
    prettyPrint (AToken _ t) = prettyPrint t

data ScanIn = ScanIn
    { getCode        :: String
    , getCurrentLine :: Int
    }
    deriving Show

type TokenScanner = Parser String String Token
type StringScanner = Parser String String String
type StateScanner = Parser String ScanIn (ListPair String AToken)

eof :: StringScanner
eof = Parser peek  where
    peek [] = Success [] []
    peek _  = Fail

identifierSymbols = ['A' .. 'Z'] <> ['a' .. 'z'] <> ['_']
keyword :: String -> StringScanner
keyword kw = exact kw <<* peek
    where peek = pure <$> single (`notElem` identifierSymbols) <|> eof

identifier :: StringScanner
identifier = some (oneOf identifierSymbols)

comment :: StringScanner
comment = exact "//" *> many (single (/= '\n'))

number :: TokenScanner
number = convert <$> numLiteral  where
    numLiteral = some $ oneOf $ ['0' .. '9'] <> ['.']
    convert x = case readMaybe x of
        Nothing -> TError ("Invalid numeric literal: " <> x)
        Just n  -> TNumber n

notRecognised :: TokenScanner
notRecognised =
    TError . ("Character not recognised: " <>) . (: []) <$> single (const True)

whitespace :: StringScanner
whitespace = some $ single (`elem` [' ', '\t', '\r'])

string :: TokenScanner
string =
    TString
        <$  quote
        <*> insidePart
        <*  quote
        <|> TError "Unterminated string"
        <$  quote
        <*  insidePart  where
    quote      = single' '"'
    insidePart = many $ single (/= '"')

anyToken :: TokenScanner
anyToken = asum
    [ TWhitespace <$ whitespace
    , TComment <$ comment
    , TLeftParen <$ single' '('
    , TRightParen <$ single' ')'
    , TLeftBrace <$ single' '{'
    , TRightBrace <$ single' '}'
    , TComma <$ single' ','
    , TDot <$ single' '.'
    , TMinus <$ single' '-'
    , TPlus <$ single' '+'
    , TSemicolon <$ single' ';'
    , TSlash <$ single' '/'
    , TStar <$ single' '*'
    , TBangEqual <$ exact "!="
    , TBang <$ single' '!'
    , TEqualEqual <$ exact "=="
    , TEqual <$ single' '='
    , TGreaterEqual <$ exact ">="
    , TGreater <$ single' '>'
    , TLessEqual <$ exact "<="
    , TLess <$ single' '<'
    , TAnd <$ keyword "and"
    , TClass <$ keyword "class"
    , TElse <$ keyword "else"
    , TFalse <$ keyword "false"
    , TFor <$ keyword "for"
    , TFun <$ keyword "fun"
    , TIf <$ keyword "if"
    , TNil <$ keyword "nil"
    , TOr <$ keyword "or"
    , TPrint <$ keyword "print"
    , TReturn <$ keyword "return"
    , TSuper <$ keyword "super"
    , TThis <$ keyword "this"
    , TTrue <$ keyword "true"
    , TVar <$ keyword "var"
    , TWhile <$ keyword "while"
    , string
    , TIdentifier <$> identifier
    , number
    , TNewline <$ exact "\n"
    , notRecognised
    ]

onState :: TokenScanner -> StateScanner
onState (Parser f) = Parser $ \(ScanIn code line) -> case f code of
    Fail -> Fail
    Error e i -> Success (ListPair [show line <> ": " <> e] []) (ScanIn i line)
    Success s i -> case s of
        TComment -> Success mempty (ScanIn i line)
        TError e ->
            Success (ListPair [show line <> ": " <> e] []) (ScanIn i line)
        TNewline    -> Success mempty (ScanIn i (line + 1))
        TWhitespace -> Success mempty (ScanIn i line)
        TString s   -> Success
            (ListPair [] [AToken line (TString s)])
            (ScanIn i (line + length (filter (== '\n') s)))
        s -> Success (ListPair [] [AToken line s]) (ScanIn i line)

scanWholeString s = extractOutput $ addEof $ runParser
    (mmany $ onState anyToken)
    (ScanIn s 1)  where
    addEof (Success o i) =
        Success (o <> ListPair [] [AToken (getCurrentLine i) TEof]) i
    addEof x = x

