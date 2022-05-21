module Analyse (analyseStatements) where
import           AST                            ( Expression(..)
                                                , Statement(..)
                                                )
import           Control.Monad                  ( unless )
import qualified Control.Monad.State           as St
import qualified Data.Map.Strict               as M
import           Data.Maybe                     ( fromMaybe )
import           Lexer                          ( AToken(..)
                                                , Token(TIdentifier)
                                                )


analyseStatements :: [Statement] -> Either [String] [Statement]
analyseStatements = flip runAnalyse initialState . analyseMany

type Analyse = St.State AnState

runAnalyse :: Analyse a -> AnState -> Either [String] a
runAnalyse a st= processResult $ St.runState a st where
    processResult (_, AnState {anErrors = x:xs}) = Left (x:xs)
    processResult (ss, _) = Right ss


data Scope = GlobalScope
           | LocalScope (M.Map String Bool) Scope
           deriving (Eq, Show)

getParentScope :: Scope -> Scope
getParentScope (LocalScope _ p) = p
getParentScope GlobalScope      = error "global scope has no parent"


data FunctionType = FNone
                  | FFunction
                  deriving (Eq, Show)


data AnState = AnState
    { anScope   :: Scope
    , anGlobals :: M.Map String Bool
    , anFunType :: FunctionType
    , anErrors  :: [String]
    }
    deriving (Eq, Show)

initialState :: AnState
initialState = AnState GlobalScope M.empty FNone [] 

getVarName :: AToken -> String
getVarName (AToken _ (TIdentifier name)) = name
getVarName _                             = error "oops"

setVarInitStatus :: Bool -> AToken -> Analyse ()
setVarInitStatus b var = do
    state <- St.get
    let scope   = anScope state
    let varName = getVarName var
    case scope of
        GlobalScope ->
            St.put state { anGlobals = M.insert varName b (anGlobals state) }
        LocalScope vars p ->
            St.put state { anScope = LocalScope (M.insert varName b vars) p }

isInitialised :: AToken -> Analyse Bool
isInitialised var = do
    scope <- St.gets anScope
    let varName = getVarName var
    return $ go varName scope
  where
    go _ GlobalScope         = True
    go v (LocalScope vars p) = fromMaybe (go v p) $ M.lookup v vars

canDeclareVar :: AToken -> Analyse Bool
canDeclareVar var = do
    scope <- St.gets anScope
    let varName = getVarName var
    case scope of
        GlobalScope       -> return True
        LocalScope vars _ -> return $ not $ M.member varName vars

beginScope :: Analyse ()
beginScope = do
    state <- St.get
    let scope = anScope state
    St.put state { anScope = LocalScope M.empty scope }

closeScope :: Analyse ()
closeScope = do
    state <- St.get
    let scope = anScope state
    St.put state { anScope = getParentScope scope }

setFunType :: FunctionType -> Analyse ()
setFunType t = do
    state <- St.get
    St.put state { anFunType = t }

logError :: String -> Analyse ()
logError e = do
    state <- St.get
    let errs = anErrors state
    St.put state { anErrors = errs <> [e] }


analyseMany :: [Statement] -> Analyse [Statement]
analyseMany ss = sequence $ analyseS <$> ss

analyseS :: Statement -> Analyse Statement
analyseS SNop                      = return SNop
analyseS (SExpression e          ) = SExpression <$> analyseE e
analyseS (SPrint l e             ) = SPrint l <$> analyseE e
analyseS (SVarDeclaration l var e) = do
    canDeclare <- canDeclareVar var
    unless canDeclare
        $  logError
        $  show l
        <> ": Tried to re-declare non-global variable '"
        <> getVarName var
        <> "'"
    setVarInitStatus False var
    e' <- analyseE e
    setVarInitStatus True var
    return $ SVarDeclaration l var e'
analyseS (SBlock l ss) = do
    beginScope
    stmts' <- sequence $ analyseS <$> ss
    closeScope
    return $ SBlock l stmts'
analyseS (SIfElse l e sa sb) = do
    e'  <- analyseE e
    sa' <- analyseS sa
    sb' <- analyseS sb
    return $ SIfElse l e' sa' sb'
analyseS (SWhile l e s) = do
    -- TODO: look into shadowing inside loops
    e' <- analyseE e
    s' <- analyseS s
    return $ SWhile l e' s'
analyseS (SFunDeclaration l fun args body) = do
    canDeclare <- canDeclareVar fun
    unless canDeclare
        $  logError
        $  show l
        <> ": Tried to re-declare non-global variable '"
        <> getVarName fun
        <> "'"
    setVarInitStatus True fun
    beginScope
    sequence_ $ setVarInitStatus True <$> args 
    state <- St.get
    let funType = anFunType state
    St.put state{anFunType = FFunction}
    body' <- sequence $ analyseS <$> body
    state' <- St.get
    St.put state {anFunType = funType}
    closeScope
    return $ SFunDeclaration l fun args body'
analyseS (SReturn l e) = do
    funType <- St.gets anFunType
    unless (funType == FFunction)
        $  logError
        $  show l
        <> ": return statement outside function"
    e' <- analyseE e
    return $ SReturn l e'

analyseE :: Expression -> Analyse Expression
analyseE e@(ELiteral _      ) = return e
analyseE (  EUnary op e     ) = EUnary op <$> analyseE e
analyseE (  EBinary ea op eb) = do
    ea' <- analyseE ea
    eb' <- analyseE eb
    return $ EBinary ea' op eb'
analyseE (  EGrouping l e  ) = EGrouping l <$> analyseE e
analyseE e@(EIdentifier var) = do
    varReady <- isInitialised var
    unless varReady
        $  logError
        $  show (getTokenLine var)
        <> ": Variable '"
        <> getVarName var
        <> "' referenced while being initialised."
    return e
analyseE (EAssignment var e) = EAssignment var <$> analyseE e
analyseE (ELogical ea op eb) = do
    ea' <- analyseE ea
    eb' <- analyseE eb
    return $ EBinary ea' op eb'
analyseE (ECall e args) = do
    e'    <- analyseE e
    args' <- sequence $ analyseE <$> args
    return $ ECall e' args'
