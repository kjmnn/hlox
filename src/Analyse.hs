{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
module Analyse
    ( analyseStatements
    ) where
import           AST                            ( Expression(..)
                                                , Statement(..)
                                                )
import           Control.Monad                  ( unless
                                                , when
                                                )
import qualified Control.Monad.State           as St
import           Data.List                      ( partition )
import qualified Data.Map.Strict               as M
import           Data.Maybe                     ( fromMaybe )
import           Lexer                          ( AToken(..)
                                                , Token(..)
                                                )


analyseStatements :: [Statement] -> Either [String] [Statement]
analyseStatements = flip runAnalyse initialState . analyseMany

type Analyse = St.State AnState

runAnalyse :: Analyse a -> AnState -> Either [String] a
runAnalyse a st = processResult $ St.runState a st  where
    processResult (_ , AnState { anErrors = x : xs }) = Left (x : xs)
    processResult (ss, _                            ) = Right ss


data Scope = GlobalScope
           | LocalScope (M.Map String Bool) Scope
           deriving (Eq, Show)

getParentScope :: Scope -> Scope
getParentScope (LocalScope _ p) = p
getParentScope GlobalScope      = error "global scope has no parent"


data AnState = AnState
    { anScope   :: Scope
    , anGlobals :: M.Map String Bool
    , anInFun   :: Bool
    , anInCls   :: Bool
    , anErrors  :: [String]
    }
    deriving (Eq, Show)

initialState :: AnState
initialState = AnState GlobalScope M.empty False False []

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
    let saved = anInFun state
    St.put state { anInFun = True }
    body'  <- sequence $ analyseS <$> body
    state' <- St.get
    St.put state { anInFun = saved }
    closeScope
    return $ SFunDeclaration l fun args body'
analyseS (SReturn l e) = do
    canReturn <- St.gets anInFun
    unless canReturn
        $  logError
        $  show l
        <> ": return statement outside function definition"
    e' <- analyseE e
    return $ SReturn l e'
analyseS (SClsDeclaration l cls@(AToken _ (TIdentifier clsName)) methods) = do
    -- We'll be desugaring this to a regular function declaration
    inClsSaved <- St.gets anInCls
    let (init, methods') = partition isInit methods
    when (length init > 1)
        $ logError
        $ show l
        <> ": multiple init methods in class definition (only first taken into account)"
    -- take just the args and body of the first init (if there are multiple)
    let (initArgs, initBody) = extract init 
    -- check for early returns inside init 
    sequence_ $ checkForReturns <$> initBody
    let constructorBody =
            -- 1) create a new object (using new_obj) and bind it to 'this'
            SVarDeclaration
                    (-1)
                    (AToken (-1) (TIdentifier "this"))
                    (ECall
                        (EIdentifier (AToken (-1) (TIdentifier "new_obj")))
                        [ELiteral (AToken (-1) (TString clsName))]
                    )
            -- 2) declare the methods inside blocks so they don't see each other (other than through 'this')
                :  (wrap <$> methods')
            -- 3) run the actual body of the init method 
                <> initBody
            -- 4) finally, return 'this' (the newly constructed object)
                <> [ SReturn
                         (-1)
                         (EIdentifier (AToken (-1) (TIdentifier "this")))
                   ]
    constructor <- analyseS $ SFunDeclaration l cls initArgs constructorBody
    state       <- St.get
    St.put state { anInCls = inClsSaved }
    return constructor
  where
    isInit (SFunDeclaration _ (AToken _ (TIdentifier "init")) _ _) = True
    isInit _ = False
    extract ((SFunDeclaration _ _ args body) : _) = (args, body)
    extract _ = ([], [])
    wrap d@(SFunDeclaration l (AToken _ (TIdentifier methodName)) _ _) = SBlock
        (-1)
        -- first declare the method
        [ d
        -- then bind it (by simply assigning to a property, since 'this' is already defined in its closure)
        , SExpression
            (EAssignment
                (EProperty (EIdentifier (AToken (-1) (TIdentifier "this")))
                           (AToken (-1) (TIdentifier methodName))
                )
                (EIdentifier (AToken (-1) (TIdentifier methodName)))
            )
        ]
    wrap _ = error "hang on, that's not a method declaration!"
    checkForReturns (SBlock _ stmts) = sequence_ $ checkForReturns <$> stmts
    checkForReturns (SIfElse _ _ stmtA stmtB) = checkForReturns stmtA >> checkForReturns stmtB
    checkForReturns (SWhile _ _ stmt) = checkForReturns stmt
    checkForReturns (SReturn l _) = logError $ show l <> ": return statement inside init method"
    checkForReturns _ = return ()
analyseS (SClsDeclaration _ _ _) =
    error "another token error that should never happen"

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
    when (getActualToken var == TIdentifier "this") $ do
        inCls <- St.gets anInCls
        unless inCls
            $  logError
            $  show (getTokenLine var)
            <> ": 'this' referenced outside method definition."
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
analyseE (EProperty e p) = do
    e' <- analyseE e
    return $ EProperty e' p
