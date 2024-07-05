{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
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
import           Data.Time.Clock.POSIX          ( getPOSIXTime )
import           Lexer
import           Parser
import           Util


newtype Compute a = Compute { unCompute :: Ex.ExceptT Exception (St.StateT ProgramState IO) a }
    deriving newtype (Functor, Applicative, Monad, Ex.MonadIO, St.MonadState ProgramState, Ex.MonadError Exception)

runCompute :: ProgramState -> Compute a -> IO (Either Exception a)
runCompute state = flip St.evalStateT state . Ex.runExceptT . unCompute


data ProgramState = ProgramState
    { prgEnv         :: Env
    , prgGlobals     :: M.Map String Int
    , prgMem         :: IM.IntMap MemCell
    , prgMagicNumber :: Int
    }

initialState = ProgramState GlobalEnv vars mem 0  where
    vars = M.fromList [("clock", -1), ("to_string", -3), ("new_obj", -5)]
    mem  = IM.fromList
        [ (-1, ValCell 1 (VFunction "clock" (-2)))
        , (-2, FunCell 1 FClock)
        , (-3, ValCell 1 (VFunction "to_string" (-4)))
        , (-4, FunCell 1 FToString)
        , (-5, ValCell 1 (VFunction "new_obj" (-6)))
        , (-6, FunCell 1 FNewObject)
        ]

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
           | VObject String Int
           deriving (Eq, Show)

instance PrettyPrint Value where
    prettyPrint (VBool True )   = "true"
    prettyPrint (VBool False)   = "false"
    prettyPrint VNil            = "nil"
    prettyPrint (VString s    ) = show s
    prettyPrint (VNumber n    ) = show n
    prettyPrint (VFunction s i) = "<function " <> s <> ": " <> show i <> ">"
    prettyPrint (VObject   s i) = "<object " <> s <> ": " <> show i <> ">"

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
showValueType (VObject   _ _) = "object"

-- used in print statements and the to_string built-in function
showValue :: Value -> String
showValue (VString s) = s
showValue v           = prettyPrint v


data Exception = RuntimeError String
               | Return Value


data Function
    = Function
        { funId       :: Int
        , funName     :: String
        , funClosure  :: Env
        , funArgNames :: [AToken]
        , funBody     :: [Statement]
        }
    | FClock
    | FToString
    | FNewObject
    deriving Show


funArgCount Function { funArgNames = args } = length args
funArgCount FClock                          = 0
funArgCount FToString                       = 1
funArgCount FNewObject                      = 1


data Object = Object
    { objId      :: Int
    , objClsName :: String
    , objClosure :: Env
    }
    deriving Show


data Env = GlobalEnv
         | NilEnv
         | LocalEnv Int (M.Map String Int) Env
         deriving Show

envId GlobalEnv        = -1
envId NilEnv           = -2
envId (LocalEnv i _ _) = i

envParent GlobalEnv        = error "global env has no parent"
envParent NilEnv           = error "NilEnv has no parent either"
envParent (LocalEnv _ _ p) = p

getEnvVars :: Env -> Compute (M.Map String Int)
-- this has to be a monadic function because of how Lox handles globals
getEnvVars GlobalEnv           = St.gets prgGlobals
getEnvVars NilEnv              = return M.empty
getEnvVars (LocalEnv _ vars _) = return vars


data MemCell = ValCell Int Value
             | FunCell Int Function
             | ObjCell Int Object
    deriving Show

memRefCount (ValCell rc _) = rc
memRefCount (FunCell rc _) = rc
memRefCount (ObjCell rc _) = rc
memSetRefCount rc (ValCell _ val) = ValCell rc val
memSetRefCount rc (FunCell _ fun) = FunCell rc fun
memSetRefCount rc (ObjCell _ obj) = ObjCell rc obj

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

instance Memable Object where
    toMem = ObjCell 0
    fromMemMaybe (ObjCell _ obj) = Just obj
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
    delete (ObjCell _ obj) = delObj obj
    delete (FunCell _ fun) = delFun fun
    delete (ValCell _ val) = delVal val
    delObj Object { objClosure = c } = decrAllRefCounts c
    delFun Function { funClosure = c } = decrAllRefCounts c
    delFun _                           = return ()
    delVal (VFunction _ a) = decrRefCount a
    delVal (VObject   _ a) = decrRefCount a
    delVal _               = return ()
    decrAllRefCounts GlobalEnv           = return ()
    decrAllRefCounts NilEnv              = return ()
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
    go l var NilEnv = notInScope l var
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

declare :: String -> Maybe Value -> Compute ()
declare var mVal = do
    state <- St.get
    let env = prgEnv state
    --Ex.liftIO $ print $ "declaring " <> var <> " in " <> show env
    vars <- getEnvVars env
    a    <- maybe produceMagicNumber return $ M.lookup var vars
    let vars' = M.insert var a vars
    state' <- St.get
    case env of
        GlobalEnv      -> St.put state' { prgGlobals = vars' }
        NilEnv         -> error "cannot declare variables in NilEnv"
        LocalEnv i _ p -> St.put state' { prgEnv = LocalEnv i vars' p }
    maybe (return ()) (void . setMem a) mVal

declareOnly :: String -> Compute ()
declareOnly var = declare var Nothing
declareAssign :: String -> Value -> Compute ()
declareAssign var val = declare var (Just val)

assign :: Int -> String -> Value -> Compute Value
assign l var val = do
    env <- St.gets prgEnv
    a   <- go l var env
    setMem a val
  where
    go l var GlobalEnv = do
        state <- St.get
        maybe (notInScope l var) return $ M.lookup var (prgGlobals state)
    go l var NilEnv = notInScope l var
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
    decrLocalRefCounts NilEnv = error "why are we exiting NilEnv"
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

eval (EAssignment (EIdentifier (AToken l (TIdentifier var))) e) = do
    val <- eval e
    assign l var val
eval (EAssignment (EProperty objExpr (AToken l (TIdentifier prop))) e) = do
    (clsName, addr) <- eval objExpr >>= extract
    val             <- eval e
    obj             <- readMem addr
    closure'        <- withEnv (objClosure obj) $ do
        declareAssign prop val
        St.gets prgEnv
    setMem addr obj { objClosure = closure' }
    return val
  where
    extract :: Value -> Compute (String, Int)
    extract (VObject s a) = return (s, a)
    extract badVal =
        Ex.throwError
            $  RuntimeError
            $  "Cannot access property on value of type "
            <> showValueType badVal
eval (EAssignment _ _) =
    error "invalid assignment target (not caught during static analysis?)"

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
    args' <- sequence $ eval <$> args
    callOuter fun args'
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
    callOuter FClock _ = VNumber . realToFrac <$> Ex.liftIO getPOSIXTime
    callOuter FToString  (x : _) = return $ VString $ showValue x
    callOuter FToString  _       = error "to_str got no arguments somehow"
    callOuter FNewObject (x : _) = case x of
        VString s -> do
            num  <- produceMagicNumber
            num2 <- produceMagicNumber
            setMem num2 $ Object num2 s (LocalEnv num M.empty NilEnv)
            return $ VObject s num2
        badVal ->
            Ex.throwError
                $  RuntimeError
                $  "Function new_obj expected a  string, got "
                <> showValueType badVal
    callOuter FNewObject _ = error "new_obj got no arguments somehow"
    callOuter fun@Function { funClosure = c } args = do
        (a, res) <-
            withEnv c
            $               withNewEnv
            $               callInner fun args
            `Ex.catchError` handleReturn
        -- bind returned value to a temporary variable to make sure it gets garbage collected
        bindTmp a
        return res
    callInner fun args = do
        let argInit = zipWith
                declareAssign
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
            NilEnv         -> error "NilEnv should never be the current env"
            LocalEnv i _ p -> St.put state { prgEnv = LocalEnv i vars' p }
eval (EProperty objExpr (AToken l (TIdentifier prop))) = do
    (clsName, addr)                 <- eval objExpr >>= extract
    Object { objClosure = closure } <- readMem addr
    withEnv closure $ readVar l prop
  where
    extract :: Value -> Compute (String, Int)
    extract (VObject s a) = return (s, a)
    extract badVal =
        Ex.throwError
            $  RuntimeError
            $  "Cannot access property on value of type "
            <> showValueType badVal

eval (EProperty _ _) = error "another wrong token error"

exec :: Statement -> Compute ()

exec SNop         = return ()

exec (SPrint _ e) = do
    val <- withNewEnv $ eval e -- evaluate in new env to garbage collect temporary values
    Ex.liftIO $ putStrLn $ showValue val


exec (SExpression e) = void $ withNewEnv $ eval e

exec (SVarDeclaration _ (AToken l (TIdentifier var)) e) = do
    val <- withNewEnv $ eval e
    void $ declareAssign var val
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
    num <- produceMagicNumber
    declareOnly name
    closure <- St.gets prgEnv
    setMem num $ Function num name closure args body
    assign undefined name (VFunction name num)
    incrAllRefCounts closure
  where
    incrAllRefCounts GlobalEnv           = return ()
    incrAllRefCounts NilEnv              = return ()
    incrAllRefCounts (LocalEnv _ vars p) = do
        sequence_ $ incrRefCount <$> M.elems vars
        incrAllRefCounts p
exec SFunDeclaration{} =
    error
        "invalid token type used in place of TIdentifier during function declaration"

exec (SReturn _ e) = do
    val <- eval e
    Ex.throwError $ Return val
exec _ = undefined
execMany :: [Statement] -> Compute ()
execMany stmts = sequence_ $ exec <$> stmts
