{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Eval where
import           AST
import           Control.Monad                  ( foldM
                                                , unless
                                                , void
                                                , when
                                                )
import qualified Control.Monad.Except          as Ex
import qualified Control.Monad.State.Strict    as St
import qualified Data.Bifunctor                as Bifunctor
                                                ( first )
import           Data.Function                  ( on )
import qualified Data.IntMap.Strict            as IM
import qualified Data.Map.Strict               as M
import           Data.Maybe                     ( fromMaybe )
import           Lexer
import           Parser
import           Util


newtype Compute a = Compute { unCompute :: Ex.ExceptT Exception (St.StateT ProgramState IO) a }
    deriving newtype (Functor, Applicative, Monad, Ex.MonadIO, St.MonadState ProgramState, Ex.MonadError Exception)

runCompute :: ProgramState -> Compute a -> IO (Either Exception a)
runCompute initialState =
    flip St.evalStateT initialState . Ex.runExceptT . unCompute


data ProgramState = ProgramState
    { prgEnv         :: Env
    , prgGlobals     :: M.Map String Int
    , prgMem         :: IM.IntMap MemCell
    , prgMagicNumber :: Int
    }

cleanState = ProgramState GlobalEnv M.empty IM.empty 0

produceMagicNumber :: Compute Int
produceMagicNumber = do
    state <- St.get
    let res = prgMagicNumber state
    St.put state { prgMagicNumber = res + 1 }
    return res


data Value = VBool Bool
           | VNil
           | VString String
           | VNumber Double
           | VFunction String Int
           deriving (Eq, Show)

instance PrettyPrint Value where
    prettyPrint (VBool True )   = "true"
    prettyPrint (VBool False)   = "false"
    prettyPrint VNil            = "nil"
    prettyPrint (VString s    ) = show s
    prettyPrint (VNumber n    ) = show n
    prettyPrint (VFunction s _) = "<function " <> s <> ">"

isTruthy :: Value -> Bool
isTruthy (VBool False) = False
isTruthy VNil          = False
-- Yes, this means 0 is truthy
isTruthy _             = True

showValueType :: Value -> String
showValueType (VBool _)       = "bool"
showValueType VNil            = "nil"
showValueType (VString _    ) = "string"
showValueType (VNumber _    ) = "number"
showValueType (VFunction _ _) = "function"


data Exception = RuntimeError String
               | Return Value


data Function = Function
    { funId       :: Int
    , funName     :: String
    , funClosure  :: Env
    , funArgNames :: [AToken]
    , funBody     :: [Statement]
    }
    deriving Show

instance Eq Function where
    (==) = (==) `on` funId

funArgCount f@Function{} = length $ funArgNames f


data Env = GlobalEnv
         | LocalEnv Int (M.Map String Int) Env
         deriving Show

envId GlobalEnv        = -1
envId (LocalEnv i _ _) = i

envParent GlobalEnv        = error "global env has no parent"
envParent (LocalEnv _ _ p) = p

getEnvVars :: Env -> Compute (M.Map String Int)
-- this has to be a monadic function because of how Lox handles globals
getEnvVars GlobalEnv           = St.gets prgGlobals
getEnvVars (LocalEnv _ vars _) = return vars


data MemCell = ValCell Int Value
             | FunCell Int Function
    deriving (Eq, Show)

memRefCount (ValCell rc _) = rc
memRefCount (FunCell rc _) = rc
memSetRefCount rc (ValCell _ val) = ValCell rc val
memSetRefCount rc (FunCell _ fun) = FunCell rc fun

-- TODO: rename this class to something saner
class Memable a where
    toMem :: a -> MemCell
    fromMemMaybe :: MemCell -> Maybe a
    fromMem :: MemCell -> a
    fromMem = fromMaybe (error "unexected data type in memcell") . fromMemMaybe

castMemable :: (Memable a, Memable b) => a -> Maybe b
castMemable = fromMemMaybe . toMem

instance Memable Value where
    toMem = ValCell 1
    fromMemMaybe (ValCell _ val) = Just val
    fromMemMaybe _               = Nothing

instance Memable Function where
    -- refcount starts at 0 and gets incremented on initial binding
    toMem = FunCell 0
    fromMemMaybe (FunCell _ fun) = Just fun
    fromMemMaybe _               = Nothing


incrRefCount :: Int -> Compute ()
incrRefCount = adjustRefCount (+ 1)

decrRefCount :: Int -> Compute ()
decrRefCount = adjustRefCount (subtract 1)

-- not to be used directly
adjustRefCount :: (Int -> Int) -> Int -> Compute ()
adjustRefCount f a = do
    state <- St.get
    let mem = prgMem state
    let cell = fromMaybe (error "invalid program memory access")
            $ IM.lookup a mem
    let rc' = f $ memRefCount cell
    St.put state { prgMem = IM.insert a (memSetRefCount rc' cell) mem }
    when (rc' == 0) $ do
        --Ex.liftIO $ print $ "NUKING " <> show cell
        delete cell
        state' <- St.get
        let mem' = prgMem state'
        St.put state' { prgMem = IM.delete a mem' }
  where
    delete (FunCell _ fun) = delFun fun
    delete (ValCell _ val) = delVal val
    delFun Function { funClosure = c } = decrAllRefCounts c
    delVal (VFunction _ a) = decrRefCount a
    delVal _               = return ()
    decrAllRefCounts GlobalEnv           = return ()
    decrAllRefCounts (LocalEnv _ vars p) = do
        sequence_ $ decrRefCount <$> M.elems vars
        decrAllRefCounts p


notInScope :: Int -> String -> Compute a
notInScope l var = Ex.throwError
    (RuntimeError $ show l <> ": variable not in scope: '" <> var <> "'")

readMem :: Memable a => Int -> Compute a
readMem a = do
    mem <- St.gets prgMem
    return $ fromMem $ IM.findWithDefault
        (error "oopsie woopsie the interpreter lost a saved value ")
        a
        mem

readVar :: Int -> String -> Compute Value
readVar l var = do
    env <- St.gets prgEnv
    go l var env
  where
    go l var GlobalEnv = do
        globals <- St.gets prgGlobals
        maybe (notInScope l var) readMem (M.lookup var globals) --`Ex.catchError` (\e -> do env <- St.gets prgEnv; Ex.liftIO $ print env;Ex.throwError e)
    go l var (LocalEnv _ vars p) =
        maybe (go l var p) readMem (M.lookup var vars)

setMem :: Memable a => Int -> a -> Compute a
setMem a x = do
    mem <- St.gets prgMem
    maybe (return ()) decrRefCount
        $   IM.lookup a mem
        >>= fromMemMaybe
        >>= extractRef
    state' <- St.get
    let mem' = prgMem state'
    St.put state' { prgMem = IM.insert a (toMem x) mem' }
    maybe (return ()) incrRefCount $ castMemable x >>= extractRef
    return x
  where
    extractRef (VFunction _ n) = Just n
    extractRef _               = Nothing

declareVar :: String -> Value -> Compute Value
declareVar var val = do
    state <- St.get
    let env = prgEnv state
    --Ex.liftIO $ print $ "declaring " <> var <> " in " <> show env
    vars <- getEnvVars env
    a    <- case env of
        GlobalEnv      -> maybe produceMagicNumber return $ M.lookup var vars
        LocalEnv _ _ _ -> produceMagicNumber  -- repeated declaration only allowed in global scope => no need to check
    let vars' = M.insert var a vars
    state' <- St.get
    case env of
        GlobalEnv      -> St.put state' { prgGlobals = vars' }
        LocalEnv i _ p -> St.put state' { prgEnv = LocalEnv i vars' p }
    setMem a val

assignVar :: Int -> String -> Value -> Compute Value
assignVar l var val = do
    env <- St.gets prgEnv
    a   <- go l var env
    setMem a val
  where
    go l var GlobalEnv = do
        state <- St.get
        maybe (notInScope l var) return $ M.lookup var (prgGlobals state)
    go l var (LocalEnv _ vars p) =
        maybe (go l var p) return $ M.lookup var vars


withNewEnv :: Compute a -> Compute a
withNewEnv action = do
    state <- St.get
    let env = prgEnv state
    i <- produceMagicNumber
    St.put state { prgEnv = LocalEnv i M.empty env }
    res    <- action
    state' <- St.get
    let env' = prgEnv state'
    decrLocalRefCounts env'
    St.put state' { prgEnv = env }  -- (the initial one)
    return res
  where
    decrLocalRefCounts GlobalEnv = error "can't exit global scope anyway"
    decrLocalRefCounts (LocalEnv _ vars _) = sequence_ $ decrRefCount <$> vars

withEnv :: Env -> Compute a -> Compute a
withEnv env action = do
    state <- St.get
    let savedEnv = prgEnv state
    St.put state { prgEnv = env }
    res    <- action
    state' <- St.get
    St.put state' { prgEnv = savedEnv }
    return res


eval :: Expression -> Compute Value
eval (ELiteral (AToken _ token)) = return $ case token of
    TTrue     -> VBool True
    TFalse    -> VBool False
    TNil      -> VNil
    TString s -> VString s
    TNumber n -> VNumber n
    _         -> error "wrong kind of token in ELiteral"

eval (EGrouping _        expression) = eval expression

eval (EUnary    operator operand   ) = do
    val <- eval operand
    operation val
  where
    operation = case getActualToken operator of
        TBang  -> evalNot
        TMinus -> evalMinus
        badOp  -> error $ "unsupported unary perator: " <> prettyShort badOp
    evalNot val = return $ VBool $ not $ isTruthy val
    evalMinus (VNumber n) = return $ VNumber (-n)
    evalMinus badVal      = typeError operator badVal
    typeError (AToken l op) badVal =
        Ex.throwError
        $  RuntimeError
        $  show l
        <> ": Cannot apply unary operator '"
        <> prettyPrint op
        <> "' to value '"
        <> prettyShort badVal
        <> "' of type '"
        <> showValueType badVal
        <> "'" :: Compute Value

eval (EBinary operandA operator operandB) = do
    valA <- eval operandA
    valB <- eval operandB
    operation valA valB
  where
    operation = case getActualToken operator of
        TMinus        -> evalArithmetic (-)
        TSlash        -> evalArithmetic (/)
        TStar         -> evalArithmetic (*)
        TPlus         -> evalPlus
        TGreater      -> evalComparison (>)
        TGreaterEqual -> evalComparison (>=)
        TLess         -> evalComparison (<)
        TLessEqual    -> evalComparison (<=)
        TEqualEqual   -> evalEquality (==)
        TBangEqual    -> evalEquality (/=)
        badOp ->
            error $ "unsupported binary operator: '" <> prettyShort badOp <> "'"
    evalPlus (  VString a) (  VString b) = return $ VString (a <> b)
    evalPlus a@(VNumber _) b@(VNumber _) = evalArithmetic (+) a b
    evalPlus badValA       badValB       = typeError operator badValA badValB
    evalArithmetic op (VNumber a) (VNumber b) = return $ VNumber (op a b)
    evalArithmetic _ badValA badValB = typeError operator badValA badValB
    evalComparison op (VNumber a) (VNumber b) = return $ VBool (op a b)
    evalComparison _ badValA badValB = typeError operator badValA badValB
    -- I do not condone these semantics, just going along with what the book says
    evalEquality op a b = return $ VBool (op a b)
    typeError (AToken l op) badValA badValB =
        Ex.throwError
        $  RuntimeError
        $  show l
        <> ": Cannot apply binary operator '"
        <> prettyPrint op
        <> "' to values '"
        <> prettyShort badValA
        <> "' and '"
        <> prettyShort badValB
        <> "' of types '"
        <> showValueType badValA
        <> "' and '"
        <> showValueType badValB
        <> "'" :: Compute Value

eval (EIdentifier (AToken l (TIdentifier var))) = readVar l var
eval (EIdentifier _                           ) = error
    "invalid token type used in place of TIdentifier during variable access"

eval (EAssignment (AToken l (TIdentifier var)) e) = do
    val <- eval e
    assignVar l var val
eval (EAssignment _ _) =
    error
        "invalid token type used in place of TIdentifier during variable assignment"

eval (ELogical operandA operator operandB) = do
    valA <- eval operandA
    if op $ isTruthy valA then return valA else eval operandB  where
    op = case getActualToken operator of
        TOr  -> id
        TAnd -> not
        badOp ->
            error
                $  "unsupported logical operator: '"
                <> prettyShort badOp
                <> "'"

eval c@(ECall e args) = do
    funMaybe <- eval e
    funId    <- verify funMaybe
    fun      <- readMem funId
    checkArgCount fun args
    args'    <- sequence $ eval <$> args
    (a, res) <- callOuter fun args'
    bindTmp a -- bind returned value to a temporary variable to make sure it gets garbage collected
    return res
  where
    verify (VFunction _ f) = return f
    verify badVal =
        Ex.throwError
        $  RuntimeError
        $  "Non-callable value in call expression: "
        <> prettyPrint badVal :: Compute Int
    checkArgCount fun args =
        let expected = funArgCount fun
            got      = length args
        in  unless (expected == got)
            $  Ex.throwError
            $  RuntimeError
            $  show (getExprLine c)
            <> ": function '"
            <> funName fun
            <> "' called with "
            <> show got
            <> " arguments instead of "
            <> show expected :: Compute ()
    callOuter fun@Function { funClosure = c } args =
        withEnv c $ withNewEnv $ callInner fun args `Ex.catchError` handleReturn
    callInner fun args = do
        let argInit = zipWith
                declareVar
                ((\(TIdentifier x) -> x) . getActualToken <$> funArgNames fun)
                args
        sequence_ argInit
        sequence_ $ exec <$> funBody fun
        Ex.throwError $ Return VNil
    handleReturn e = case e of
        (Return val) -> do
            -- save the returned value in case it's a reference type
            -- (so the function / object doesn't get garbage collected)
            a <- produceMagicNumber
            setMem a val
            return (a, val)
        otherException -> Ex.throwError otherException :: Compute (Int, Value)
    bindTmp a = do
        state <- St.get
        let env = prgEnv state
        vars <- getEnvVars env
        let vars' = M.insert ('#' : show a) a vars
        case env of
            GlobalEnv      -> St.put state { prgGlobals = vars' }
            LocalEnv i _ p -> St.put state { prgEnv = LocalEnv i vars' p }


exec :: Statement -> Compute ()

exec SNop         = return ()

exec (SPrint _ e) = do
    val <- withNewEnv $ eval e -- evaluate in new end to garbage collect temporary values
    Ex.liftIO $ putStrLn $ showValue val
  where
    showValue (VString s) = s
    showValue v           = prettyPrint v

exec (SExpression e) = void $ withNewEnv $ eval e

exec (SVarDeclaration _ (AToken l (TIdentifier var)) e) = do
    val <- withNewEnv $ eval e
    void $ declareVar var val
exec (SVarDeclaration _ _ _) =
    error
        "invalid token type used in place of TIdentifier during variable declaration"

exec (SBlock _ stmts         ) = withNewEnv $ execMany stmts

exec (SIfElse _ e stmtA stmtB) = do
    val <- withNewEnv $ eval e
    exec $ if isTruthy val then stmtA else stmtB

exec (SWhile _ e stmt) = withNewEnv loop  where
    loop = do
        val <- eval e
        when (isTruthy val) $ exec stmt >> loop

exec (SFunDeclaration _ (AToken _ (TIdentifier name)) args body) = do
    num     <- produceMagicNumber
    closure <- St.gets prgEnv
    incrAllRefCounts closure
    setMem num $ Function num name closure args body
    void $ declareVar name (VFunction name num)
  where
    incrAllRefCounts GlobalEnv           = return ()
    incrAllRefCounts (LocalEnv _ vars p) = do
        sequence_ $ incrRefCount <$> M.elems vars
        incrAllRefCounts p
exec SFunDeclaration{} =
    error
        "invalid token type used in place of TIdentifier during function declaration"

exec (SReturn _ e) = do
    val <- eval e
    Ex.throwError $ Return val

execMany :: [Statement] -> Compute ()
execMany stmts = sequence_ $ exec <$> stmts
