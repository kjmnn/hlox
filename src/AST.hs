{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
module AST
    ( Expression(..)
    , Statement(..)
    , getExprLine
    , getStmtLine
    , parseExpression
    , parseStatements
    ) where

import           Control.Applicative            ( Alternative(..)
                                                , liftA2
                                                )
import           Data.Either                    ( isLeft )
import           Data.Foldable                  ( asum )
import           Data.List                      ( partition )
import           Lexer                          ( AToken(..)
                                                , Token(..)
                                                , scanWholeString
                                                )
import           Parser
import           Util

data Statement = SNop
               | SExpression Expression
               | SPrint Int Expression
               | SVarDeclaration Int AToken Expression
               | SBlock Int [Statement]
               | SIfElse Int Expression Statement Statement
               | SWhile Int Expression Statement
               | SFunDeclaration Int AToken [AToken] [Statement]
               | SReturn Int Expression
               | SClsDeclaration Int AToken [Statement]
               deriving (Eq, Show)

getStmtLine :: Statement -> Int
getStmtLine SNop = error "there's no reason to call this on a nop"
getStmtLine (SExpression e          ) = getExprLine e
getStmtLine (SPrint l _             ) = l
getStmtLine (SVarDeclaration l _ _  ) = l
getStmtLine (SBlock l _             ) = l
getStmtLine (SIfElse l _ _ _        ) = l
getStmtLine (SWhile l _ _           ) = l
getStmtLine (SFunDeclaration l _ _ _) = l
getStmtLine (SReturn l _            ) = l
getStmtLine (SClsDeclaration l _ _  ) = l

data Expression = ELiteral AToken
                | EUnary AToken Expression
                | EBinary Expression AToken Expression
                | EGrouping Int Expression
                | EIdentifier AToken
                | EAssignment Expression Expression
                | ELogical Expression AToken Expression
                | ECall Expression [Expression]
                | EProperty Expression AToken
                deriving (Eq, Show)

getExprLine :: Expression -> Int
getExprLine (ELiteral l     ) = getTokenLine l
getExprLine (EUnary op _    ) = getTokenLine op
getExprLine (EBinary e _ _  ) = getExprLine e
getExprLine (EGrouping l _  ) = l
getExprLine (EIdentifier i  ) = getTokenLine i
getExprLine (EAssignment e _) = getExprLine e
getExprLine (ELogical e _ _ ) = getExprLine e
getExprLine (ECall e _      ) = getExprLine e
getExprLine (EProperty  e _      ) = getExprLine e

instance PrettyPrint Expression where
    prettyPrint (ELiteral t) = prettyPrint t
    prettyPrint (EUnary t e) =
        "(" <> prettyPrint t <> " " <> prettyPrint e <> ")"
    prettyPrint (EBinary e1 t e2) =
        "("
            <> prettyPrint t
            <> " "
            <> prettyPrint e1
            <> " "
            <> prettyPrint e2
            <> ")"
    prettyPrint (EGrouping _ e) = "(group " <> prettyPrint e <> ")"
    prettyPrint (EIdentifier t) = prettyPrint t
    prettyPrint (EAssignment t e) =
        "(= " <> prettyPrint t <> " " <> prettyPrint e <> ")"
    prettyPrint (ELogical e1 t e2) = prettyPrint (EBinary e1 t e2)
    prettyPrint (ECall e es) =
        "(" <> prettyPrint e <> " " <> unwords (prettyPrint <$> es) <> ")"
    prettyPrint (EProperty e t) =
        "(." <> prettyPrint t <> " " <> prettyPrint e <> ")"
    --prettyPrint _ = "MY SPOON IS TOO BIG"

singleT p = single (p . getActualToken)

singleT' x = singleT (== x)

oneOfT xs = single ((`elem` xs) . getActualToken)

isIdentifier (TIdentifier _) = True
isIdentifier _               = False

astParseError :: String -> Parser String [AToken] o
astParseError hint = parseError fmt  where
    fmt (AToken l TEof) = show l <> ": Parse error at EOF" <> hint
    fmt (AToken l x) =
        show l <> ": Parse error at '" <> prettyShort x <> "'" <> hint

binaryR
    :: (Expression -> AToken -> Expression -> Expression)
    -> Parser String [AToken] Expression
    -> Parser String [AToken] AToken
    -> Parser String [AToken] Expression
binaryR constructor subexpr operator =
    constructor
        <$> subexpr
        <*> operator
        <*> binaryR constructor subexpr operator
        <|> subexpr

binaryL
    :: forall a
     . (Expression -> a -> Expression -> Expression)
    -> Parser String [AToken] Expression
    -> Parser String [AToken] a
    -> Parser String [AToken] Expression
binaryL constructor subexpr operator = process <$> subexpr <*> many
    ((,) <$> operator <*> subexpr)
  where
    process :: Expression -> [(a, Expression)] -> Expression
    process = foldl (\x (y, z) -> constructor x y z)

failOn :: Token -> Parser e [AToken] o -> Parser e [AToken] o
failOn t (Parser f) = Parser $ \x -> case x of
    (AToken _ t' : _) -> if t == t' then Fail else f x
    _                 -> f x

expectSemicolon = semicolon <|> missingSemicolon  where
    semicolon        = singleT' TSemicolon
    missingSemicolon = astParseError " (missing semicolon?)"

--- TODO: write some tests
topStatement :: Parser String [AToken] Statement
topStatement = failOn TEof $ sync declaration  where
    -- TODO: sync after block statements
    sync (Parser f) = Parser $ \x -> case f x of
        Error e i -> Error
            e
            ( dropSemicolon
            . dropWhile (\(AToken _ t) -> t `notElem` [TEof, TSemicolon])
            $ i
            )
        res -> res
    dropSemicolon (AToken _ TSemicolon : ts) = ts
    dropSemicolon ts                         = ts

declaration :: Parser String [AToken] Statement
declaration =
    varDeclaration
        <*  expectSemicolon
        <|> funDeclaration
        <|> clsDeclaration
        <|> statement

varDeclaration :: Parser String [AToken] Statement
varDeclaration =
    SVarDeclaration
        <$> (getTokenLine <$> singleT' TVar)
        <*> singleT isIdentifier
        <*  singleT' TEqual
        <*> expression
        <|> SVarDeclaration
        <$> (getTokenLine <$> singleT' TVar)
        <*> singleT isIdentifier
        <*> pure (ELiteral (AToken 0 TNil))

funDeclaration :: Parser String [AToken] Statement
funDeclaration =
    SFunDeclaration
        <$> (getTokenLine <$> singleT' TFun)
        <*> singleT isIdentifier
        <*  singleT' TLeftParen
        <*> args
        <*  singleT' TRightParen
        <*  singleT' TLeftBrace
        <*> many (failOn TRightBrace topStatement)
        <*  singleT' TRightBrace
  where
    args =
        liftA2 (:)
               (singleT isIdentifier)
               (many $ singleT' TComma *> singleT isIdentifier)
            <|> pure []

clsDeclaration :: Parser String [AToken] Statement
clsDeclaration =
    SClsDeclaration
        <$> (getTokenLine <$> singleT' TClass)
        <*> singleT isIdentifier
        <*  singleT' TLeftBrace
        <*> many funDeclaration
        <*  singleT' TRightBrace

statement :: Parser String [AToken] Statement
statement =
    blockStmt
        <|> whileStmt
        <|> forStmt
        <|> ifElseStmt
        <|> ifStmt
        --TODO: think about Nop and semicolons
        <|> nop
        <|> (printStmt <|> returnStmt <|> expressionStmt)
        <*  expectSemicolon
  where
    nop            = SNop <$ singleT' TSemicolon
    nop'           = SNop <$ expectSemicolon
    printStmt = SPrint <$> (getTokenLine <$> singleT' TPrint) <*> expression
    expressionStmt = SExpression <$> expression
    blockStmt =
        SBlock
            <$> (getTokenLine <$> singleT' TLeftBrace)
            <*> many (failOn TRightBrace topStatement)
            <*  singleT' TRightBrace
    ifStmt     = ifCommon <*> pure SNop
    ifElseStmt = ifCommon <* singleT' TElse <*> statement
    ifCommon =
        SIfElse
            <$> (getTokenLine <$> singleT' TIf)
            <*  singleT' TLeftParen
            <*> expression
            <*  singleT' TRightParen
            --  vvv this part might be a bit sketchy
            <*> statement
    whileStmt =
        SWhile
            <$> (getTokenLine <$> singleT' TWhile)
            <*  singleT' TLeftParen
            <*> expression
            <*  singleT' TRightParen
            <*> statement
    forStmt =
        desugarFor
            <$> (getTokenLine <$> singleT' TFor)
            <*  singleT' TLeftParen
            <*> forInit
            <*> forExpr -- condition
            <*> forExpr -- increment
            <*  singleT' TRightParen
            <*> statement
    forInit =
        (varDeclaration <|> SExpression <$> expression)
            <*  singleT' TSemicolon
            <|> nop'
    forExpr      = (expression <|> noExpression) <* expectSemicolon
    noExpression = pure $ ELiteral (AToken 0 TNil)
    desugarFor line init cond incr body = SBlock
        line
        [ init
        , SWhile line cond (SBlock (getStmtLine body) [body, SExpression incr])
        ]
    returnStmt = SReturn <$> (getTokenLine <$> singleT' TReturn) <*> expression


manyStatements :: Parser String [AToken] (ListPair String Statement)
manyStatements = mmany statementWrapped  where
    statementWrapped = Parser $ \x -> case runParser topStatement x of
        Fail        -> Fail
        Error   e i -> Success (ListPair [e] []) i
        Success s i -> Success (ListPair [] [s]) i

expression :: Parser String [AToken] Expression
expression = assignment

assignment =
    EAssignment
        <$> call <* singleT' TEqual
        <*> assignment
        <|> logicalOr  {-where
    check (Parser f) = Parser $ \x -> case f x of
        Fail                      -> Fail
        Error   e               i -> Error e i
        Success (EIdentifier t) i -> Success t i
        Success e               i -> Error
            (show (getTokenLine (head x)) <> ": Invalid assignment target")
            i-}
logicalOr = binaryR ELogical logicalAnd (singleT' TOr)

logicalAnd = binaryR ELogical equality (singleT' TAnd)

equality = binaryL EBinary comparison operator
    where operator = oneOfT [TEqualEqual, TBangEqual]

comparison = binaryL EBinary term operator
    where operator = oneOfT [TLess, TLessEqual, TGreater, TGreaterEqual]

term = binaryL EBinary factor operator where operator = oneOfT [TPlus, TMinus]

factor = binaryL EBinary unary operator
    where operator = oneOfT [TSlash, TStar]

unary = EUnary <$> operator <*> unary <|> call
    where operator = oneOfT [TBang, TMinus]

call = process <$> primary <*> many (Left <$> argList <|> Right <$> property)  where
    argList = singleT' TLeftParen *> args <* singleT' TRightParen
    args =
        liftA2 (:)
               (failOn TRightParen expression)
               (many $ failOn TRightParen $ singleT' TComma *> expression)
            <|> pure []
    property = singleT' TDot *> singleT isIdentifier
    process :: Expression -> [Either [Expression] AToken] -> Expression
    process e [] = e
    process e cs = foldl go e cs
    go e (Left as) = ECall e as
    go e (Right p) = EProperty e p


primary = grouping <|> literal <|> identifier <|> astParseError ""

identifier = EIdentifier <$> singleT isIdentifier

grouping =
    EGrouping <$> (getTokenLine <$> leftParen) <*> expression <* rightParen  where
    leftParen  = singleT' TLeftParen
    rightParen = singleT' TRightParen

literal = ELiteral <$> (oneOfT [TTrue, TFalse, TNil] <|> string <|> number)  where
    string = singleT isString
    isString (TString _) = True
    isString _           = False
    number = singleT isNumber
    isNumber (TNumber _) = True
    isNumber _           = False

parseExpression = runParser expression
parseStatements = runParser manyStatements
