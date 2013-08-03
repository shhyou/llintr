{-# LANGUAGE FlexibleContexts #-}

{-
  An abstract machine for call-by-value* lambda calculus.
  https://gist.github.com/suhorng/5355222
  https://gist.github.com/suhorng/5355378

  The codes are 'flatten'. Environment/stack manipulations are changed.
  So this looks more like a machine, and now implementing the machine
  in C is quite straightforward.

  The machine codes might lead to uncovered transition now.

  *: arguments are evaluated precede function body
-}

import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity
import Control.Applicative (Applicative, (<*>), (<$>), pure)
import System.IO -- for writeAll
import Data.Word
import Data.List (elemIndex, intercalate, partition, nub, (\\))
import qualified Data.Map as Map

data Expr = Var String
          | Lambda String Expr
          | Let String Expr Expr
          | Ap Expr Expr
          | I Int
          | Plus Expr Expr
          | Times Expr Expr
          | IfZ Expr Expr Expr
          | Fix Expr
          deriving Show

data Code = Access Word64 Code
          | Function Code Code
          | Save Code
          | Restore Code
          | Call Code
          | Return
          | Halt

          | ConstInt Int Code
          | Add Code
          | Mul Code
          | BranchNZ Code Code Code -- the 3rd Code is for compilation usage only
          | Jump Code               -- Jump should only be used in conjunction
                                    -- with BranchNZ (in both branch)

data Value = Closure Env Code
           | IntV Int

type Env = [Value]

type Values = [Value]
type Stack = [Either Code Env]

type Machine = (Code, Values, Stack, Env)

data Type = TypeVar Int
          | IntType
          | Arrow Type Type

type Context = Map.Map Int Type

instance Show Code where
  show (Access m c) = "Var " ++ show m ++ "; " ++ show c
  show (Function c e) = "Function {" ++ show e ++ "}; " ++ show c
  show (Save c) = "Save; " ++ show c
  show (Restore c) = "Restore; " ++ show c
  show (Call c) = "Call; " ++ show c
  show Return = "Return;"
  show Halt = "Halt;"

  show (ConstInt m c) = "ConstInt " ++ show m ++ "; " ++ show c
  show (Add c) = "Add; " ++ show c
  show (Mul c) = "Mul; " ++ show c
  show (BranchNZ e1 e2 c) = "BranchNZ Z{" ++ show e1 ++ "} NZ{"
                            ++ show e2 ++ "}; " ++ show c
  show (Jump _) = "Jump;"

instance Show Value where
  show (Closure env c) = "(\\ -> " ++ show c ++ ")"
  show (IntV m) = show m

typeVars :: Type -> [Int]
typeVars t = nub $ typeVars' t []
  where typeVars' (TypeVar v) = (v:)
        typeVars' IntType = id
        typeVars' (Arrow t1 t2) = typeVars' t2 . typeVars' t1

prettyPrintType :: Type -> Bool -> String
prettyPrintType (TypeVar n) _ = "v" ++ show n
prettyPrintType IntType _ = "Int"
prettyPrintType (Arrow t1 t2) pos = lparen ++ prettyPrintType t1 True ++
                                    " -> " ++ prettyPrintType t2  False ++ rparen
  where (lparen, rparen) | pos       = ("(", ")")
                         | otherwise = ("", "")


prettyPrintQuantification :: Type -> String
prettyPrintQuantification = ("forall" ++) . concat . map ((" v" ++) . show) . typeVars

instance Show Type where
  show t = prettyPrintType t False

assertLookup :: (Eq a, Show a) => a -> [(a,b)] -> b
assertLookup x env =
  case lookup x env of
    Just val -> val
    Nothing  -> error ("Unbound variable " ++ show x)

deepFind :: Context -> Type -> Type
deepFind _ IntType         = IntType
deepFind cxt (TypeVar v)   = case Map.lookup v cxt of
                              Just t  -> deepFind cxt t
                              Nothing -> TypeVar v
deepFind cxt (Arrow t1 t2) = Arrow (deepFind cxt t1) (deepFind cxt t2)

occursIn :: Context -> Int -> Type -> Bool
occursIn cxt v (TypeVar v') =
  case deepFind cxt (TypeVar v') of
    TypeVar v'' -> v == v''
    t'' -> occursIn cxt v t''
occursIn _ _ IntType = False
occursIn cxt v (Arrow t1 t2) = occursIn cxt v t1 || occursIn cxt v t2

solve :: (Applicative m, MonadState Context m, MonadError String m)
      => Type 
      -> Type
      -> m ()
solve IntType IntType =
  return ()
solve (Arrow dom1 codom1) (Arrow dom2 codom2) = do
  solve dom1 dom2
  solve codom1 codom2
solve (TypeVar v1) t2 = do
  cxt <- get
  case Map.lookup v1 cxt of
    Just t1 -> solve t1 t2
    Nothing -> case deepFind cxt t2 of
                TypeVar v2 | v1 == v2 -> return ()
                t2' -> if occursIn cxt v1 t2'
                       then throwError . strMsg $ "Unable to construct type " ++ show (TypeVar v1) ++ " = " ++ show t2'
                                                ++ "\nIn the context of: " ++ show cxt
                       else put $ Map.insert v1 t2' cxt
solve t1 (TypeVar v2) =
  solve (TypeVar v2) t1
solve t1 t2 = do
  cxt <- get
  throwError . strMsg $ "Unable to solve " ++ show t1 ++ " with " ++ show t2
                      ++ "\nin the context of " ++ show cxt

nextVar :: MonadState Int m
        => m Int
nextVar = modify (+1) >> get

instantiate :: MonadState Int m
        => Type
        -> [Int]
        -> m Type
instantiate t oldVars = do
  vars <- mapM (const nextVar) oldVars
  return (substitute (zip oldVars vars) t)
  where substitute _ IntType = IntType
        substitute lst (TypeVar v) = case lookup v lst of
                                      Just v' -> TypeVar v'
                                      Nothing -> TypeVar v
        substitute lst (Arrow t1 t2) = Arrow (substitute lst t1) (substitute lst t2)

buildUp :: (Applicative m, MonadState Context m, MonadError String m)
        => [(String, Int)]  -- context
        -> [(String, (Type, [Int]))] -- polymorphic type
        -> Expr
        -> StateT Int m Type
buildUp _ _ (I _) =
  return IntType
buildUp cxt poly (Var x) =
  case lookup x cxt of
    Just v -> deepFind <$> (lift get) <*> pure (TypeVar v)
    Nothing -> uncurry instantiate (assertLookup x poly)
buildUp cxt poly (Lambda x e) = do
  va <- nextVar
  b <- buildUp ((x,va):cxt) poly e
  deepFind <$> (lift get) <*> pure (Arrow (TypeVar va) b)
buildUp cxt poly (Ap e1 e2) = do
  a2b <- buildUp cxt poly e1
  a <- buildUp cxt poly e2
  b <- TypeVar <$> nextVar
  lift $ solve a2b (Arrow a b)
  deepFind <$> (lift get) <*> pure b
buildUp cxt poly (Let x e body) = do
  t <- buildUp cxt poly e
  buildUp cxt ((x, (t, typeVars t \\ map snd cxt)):poly) body
buildUp cxt poly (Plus e1 e2) = do
  t1 <- buildUp cxt poly e1
  t2 <- buildUp cxt poly e2
  lift $ solve t1 IntType
  lift $ solve t2 IntType
  return IntType
buildUp cxt poly (Times e1 e2) = do
  t1 <- buildUp cxt poly e1
  t2 <- buildUp cxt poly e2
  lift $ solve t1 IntType
  lift $ solve t2 IntType
  return IntType
buildUp cxt poly (IfZ e0 e1 e2) = do
  t0 <- buildUp cxt poly e0
  t1 <- buildUp cxt poly e1
  t2 <- buildUp cxt poly e2
  lift $ solve t0 IntType
  lift $ solve t1 t2
  deepFind <$> (lift get) <*> pure t1
buildUp cxt poly (Fix e) = do
  a2a <- buildUp cxt poly e
  a <- TypeVar <$> nextVar
  lift $ solve a2a (Arrow a a)
  deepFind <$> (lift get) <*> pure a

runMonads :: s -> StateT s (ErrorT String Identity) a -> Either String (a, s)
runMonads initState = runIdentity . runErrorT . flip runStateT initState

typeInfer = fmap (fst . fst) . runMonads Map.empty . flip runStateT 0 . buildUp [] []

translate' :: [String] -> Expr -> Code -> Code
translate' var (Var x) c = Access (fromIntegral  idx) c
  where idx = maybe (error ("Unbound variable: " ++ x)) id (x `elemIndex` var)
translate' var (Lambda x e) c = Function c (translate' (x:var) e Return)
translate' var (Let x e1 e2) c = translate' var (Ap (Lambda x e2) e1) c
translate' var (Ap e0 e1) c = Save $
                              translate' var e1 $
                              Restore $
                              translate' var e0 $
                              Call $
                              c
translate' _ (I n) c = ConstInt n c
translate' var (Plus e1 e2) c = Save $
                                translate' var e2 $
                                Restore $
                                translate' var e1 $
                                Add $
                                c
translate' var (Times e1 e2) c = Save $
                                 translate' var e2 $
                                 Restore $
                                 translate' var e1 $
                                 Mul $
                                 c
translate' var (IfZ e0 e1 e2) c = Save $
                                  translate' var e0 $
                                  Restore $
                                  BranchNZ (translate' var e1 (Jump c))
                                           (translate' var e2 (Jump c))
                                           c
translate' var (Fix e) c = translate' var (Ap pY e) c

{-
  Save; e2; Restore; e1; Call; rest

  Variant of the defunctionalized continuation:
    Empty
  | Arg0 Env Code Cont
  | Jump Value Cont

  where the save/restore of Env is writing out explicitly.
-}

type EnvClean = Bool

{-
  remove redundant Save/Restore instruction of the form
        Save; e1; Restore; rest
  where e1 does not modify the environment
  (that is, doesn't contain function calls)

  Note that Save/Restore pair and BranchNZ/Jump/Jump tuple
  should not have interleaved.
-}
removeEnv :: EnvClean -> Code -> ([EnvClean] -> Code -> Code) -> Code
removeEnv clean (Access m c) k =
  removeEnv clean c $ \bs rest ->
  k bs (Access m rest)
removeEnv clean (Function c e) k =
  case c of
    Call c' -> removeEnv clean c' $ \bs rest ->
               k bs (Function (Call rest) (removeEnv True e (const id)))
    c''     -> removeEnv clean c'' $ \bs rest ->
               k bs (Function rest (removeEnv True e (const id)))
removeEnv _ (Save c) k =
  removeEnv True c $ \bs rest ->
  let c' = case bs of
             True:_  -> rest
             False:_ -> Save rest
             _       -> error "Mismatched Save/Restore pair"
  in k (tail bs) c'
removeEnv clean (Restore c) k =
  removeEnv True c $ \bs rest ->
  let c' = case clean of
             True -> rest
             False -> Restore rest
  in k (clean:bs) c'
removeEnv _ (Call c) k =
  removeEnv False c $ \bs rest ->
  k bs (Call rest)

removeEnv clean (ConstInt m c) k =
  removeEnv clean c $ \bs rest ->
  k bs (ConstInt m rest)
removeEnv clean (Add c) k =
  removeEnv clean c $ \bs rest ->
  k bs (Add rest)
removeEnv clean (Mul c) k =
  removeEnv clean c $ \bs rest ->
  k bs (Mul rest)
removeEnv clean (BranchNZ e1 e2 c) k =
  removeEnv clean e1 $ \[e1clean] e1' ->
  removeEnv clean e2 $ \[e2clean] e2' ->
  removeEnv (e1clean && e2clean) c $ \bs rest ->
  k bs (BranchNZ e1' e2' rest)
removeEnv clean (Jump c) k =
  k [clean] (Jump c)

removeEnv _ c k = k [] c

translate e = removeEnv undefined (translate' [] e Halt) (const id)

run :: Machine -> Value
run (Access m c, vs, stk, env) =
  run (c, (env !! (fromIntegral  m)):vs, stk, env)
run (Function c e, vs, stk, env) =
  run (c, (Closure env e):vs, stk, env)
run (Save c, vs, stk, env) =
  run (c, vs, (Right env):stk, env)
run (Restore c, vs, (Right env):stk, _) =
  run (c, vs, stk, env)
run (Call c, (Closure env' e'):v:vs, stk, _) =
  run (e', vs, (Left c):stk, v:env')
run (Return, vs, (Left c):stk, env) =
  run (c, vs, stk, env)
run (Halt, v:_, _, _) = v

run (ConstInt m c, vs, stk, env) =
  run (c, (IntV m):vs, stk, env)
run (Add c, (IntV m2):(IntV m1):vs, stk, env) =
  run (c, (IntV (m1+m2)):vs, stk, env)
run (Mul c, (IntV m2):(IntV m1):vs, stk, env) =
  run (c, (IntV (m1*m2)):vs, stk, env)
run (BranchNZ e1 e2 _, (IntV m):vs, stk, env) =
  run (if m == 0 then e1 else e2, vs, stk, env)
run (Jump c, vs, stk, env) =
  run (c, vs, stk, env)

run _ = error "Undefined state transition"

dbgmm :: Machine -> IO ()
dbgmm (c, vs, stk, env) =
  putStrLn text
  where this_code (Access m _) = "Access " ++ show m
        this_code (Function _ _) = "Function"
        this_code (Save _) = "Save"
        this_code (Restore _) = "Restore"
        this_code (Call _) = "Call"
        this_code Return = "Return"
        this_code Halt = "Halt"
        this_code (ConstInt m _) = "ConstInt " ++ show m
        this_code (Add _) = "Add"
        this_code (Mul _) = "Mul"
        this_code (BranchNZ _ _ _) = "BranchNZ"
        this_code (Jump _) = "Jump"

        show_stk (Left _) = "AddrType"
        show_stk (Right _) = "EnvType"

        show_val (Closure _ _) = "<function>"
        show_val (IntV m) = show m

        text = "op code: " ++ this_code c ++ "\n" ++
               "values: " ++ intercalate " " (map show_val vs) ++ "\n" ++
               "stk: " ++ intercalate " " (map show_stk stk) ++ "\n" ++
               "env: " ++ intercalate " " (map show_val env) ++ "\n"
dbg :: Machine -> IO Value
dbg mm@(Access m c, vs, stk, env) = do
  dbgmm mm
  dbg (c, (env !! (fromIntegral  m)):vs, stk, env)
dbg mm@(Function c e, vs, stk, env) = do
  dbgmm mm
  dbg (c, (Closure env e):vs, stk, env)
dbg mm@(Save c, vs, stk, env) = do
  dbgmm mm
  dbg (c, vs, (Right env):stk, env)
dbg mm@(Restore c, vs, (Right env):stk, _) = do
  dbgmm mm
  dbg (c, vs, stk, env)
dbg mm@(Call c, (Closure env' e'):v:vs, stk, _) = do
  dbgmm mm
  dbg (e', vs, (Left c):stk, v:env')
dbg mm@(Return, vs, (Left c):stk, env) = do
  dbgmm mm
  dbg (c, vs, stk, env)
dbg mm@(Halt, v:_, _, _) =  do
  dbgmm mm
  return v

dbg mm@(ConstInt m c, vs, stk, env) = do
  dbgmm mm
  dbg (c, (IntV m):vs, stk, env)
dbg mm@(Add c, (IntV m2):(IntV m1):vs, stk, env) = do
  dbgmm mm
  dbg (c, (IntV (m1+m2)):vs, stk, env)
dbg mm@(Mul c, (IntV m2):(IntV m1):vs, stk, env) = do
  dbgmm mm
  dbg (c, (IntV (m1*m2)):vs, stk, env)
dbg mm@(BranchNZ e1 e2 _, (IntV m):vs, stk, env) = do
  dbgmm mm
  dbg (if m == 0 then e1 else e2, vs, stk, env)
dbg mm@(Jump c, vs, stk, env) = do
  dbgmm mm
  dbg (c, vs, stk, env)

dbg _ = error "Undefined state transition"

main = dbg (translate $ (IfZ (I 0) (Ap (Ap pY (Lambda "self" $ Lambda "n" $ I 514)) (I 0)) (I 3)), [], [], [])

go c = run (c, [], [], [])

-- \x. x
pid = Lambda "x" (Var "x")

-- \f s. s
pzero = Lambda "f" (Lambda "s" (Var "s"))

-- \n. \f s. f (n f s)
psuc = Lambda "n" (Lambda "f" (Lambda "s"
        (Ap (Var "f")
         (Ap (Ap (Var "n") (Var "f")) (Var "s")))))

-- \m n. m pSuc n
padd = Lambda "m" (Lambda "n"
        (Ap (Ap (Var "m") psuc) (Var "n")))

-- \p q. p
p1 = Lambda "p" (Lambda "q" (Var "p"))

-- \p q. q
p2 = Lambda "p" (Lambda "q" (Var "q"))

-- \f x y. f y x
pflip = Lambda "f" (Lambda "x" (Lambda "y" (Ap (Ap (Var "f") (Var "y")) (Var "x"))))

pZ515pred = Lambda "n" (IfZ (Var "n") (I 514) (Plus (Var "n") (I (-1))))

-- test
ptest1 = Ap (Ap padd (Ap psuc (Ap psuc pzero))) (Ap psuc pzero)
ptest2 = Ap (Ap p1 pzero) pid
ptest3 = Ap (Ap p1 pid) p1
ptest4 = Ap (Ap (Ap pflip p1) pid) p1
ptest5 = Ap pZ515pred (I 8)
ptest6 = Ap pZ515pred (I 0)

type AnnotateLabel = Int
data AnnotatedCode = AAccess Int Word64 AnnotatedCode
                   | AFunction Int AnnotatedCode AnnotateLabel AnnotatedCode
                   | ASave Int AnnotatedCode
                   | ARestore Int AnnotatedCode
                   | ACall Int AnnotatedCode
                   | AReturn Int
                   | AHalt Int
                   | AConstInt Int Int AnnotatedCode
                   | AAdd Int AnnotatedCode
                   | AMul Int AnnotatedCode
                   | ABranchNZ Int AnnotatedCode               -- e1
                                   AnnotateLabel AnnotatedCode -- e2 label, e2
                                   AnnotateLabel AnnotatedCode -- c label, c
                   | AJump Int AnnotateLabel
                   deriving (Show)

newLabel :: StateT [Int] (State Int) AnnotateLabel
newLabel = lift $ (modify (+1)) >> (liftM (subtract 1) get)

codeSize :: AnnotatedCode -> Int
codeSize (AAccess size _ _) = size
codeSize (AFunction size _ _ _) = size
codeSize (ASave size _) = size
codeSize (ARestore size _) = size
codeSize (ACall size _) = size
codeSize (AReturn size) = size
codeSize (AHalt size) = size
codeSize (AConstInt size _ _) = size
codeSize (AAdd size _) = size
codeSize (AMul size _) = size
codeSize (ABranchNZ size _ _ _ _ _) = size
codeSize (AJump size _) = size

annotate' :: Code -> StateT [Int] (State Int) AnnotatedCode
annotate' (Access m c) = do
  rest <- annotate' c
  return $ AAccess (codeSize rest + 2) m rest
annotate' (Function c e) = do
  name <- newLabel
  rest <- annotate' c
  function <- annotate' e
  return $ AFunction (codeSize rest + codeSize function + 2) rest name function
annotate' (Save c) = do
  rest <- annotate' c
  return $ ASave (codeSize rest + 1) rest
annotate' (Restore c) = do
  rest <- annotate' c
  return $ ARestore (codeSize rest + 1) rest
annotate' (Call c) = do
  rest <- annotate' c
  return $ ACall (codeSize rest + 1) rest
annotate' Return = do
  return $ AReturn 1
annotate' Halt = do
  return $ AHalt 1
annotate' (ConstInt m c) = do
  rest <- annotate' c
  return $ AConstInt (codeSize rest + 2) m rest
annotate' (Add c) = do
  rest <- annotate' c
  return $ AAdd (codeSize rest + 1) rest
annotate' (Mul c) = do
  rest <- annotate' c
  return $ AMul (codeSize rest + 1) rest
annotate' (BranchNZ e1 e2 c) = do
  restLabel <- newLabel
  nzLabel <- newLabel
  modify (restLabel :)
  zCode <- annotate' e1
  nzCode <- annotate' e2
  restCode <- annotate' c
  modify tail
  return $ ABranchNZ (codeSize zCode + codeSize nzCode + codeSize restCode + 2)
                     zCode
                     nzLabel nzCode
                     restLabel restCode
annotate' (Jump _) = do
  jumpLabel <- liftM head get
  return $ AJump 2 jumpLabel

annotate :: Code -> AnnotatedCode
annotate c = fst $ fst $ runState (runStateT (annotate' c) []) 0

data FlatCode = FAccess Word64 | FFunction AnnotateLabel | FSave | FRestore
              | FCall | FTailCall | FReturn | FHalt | FConstInt Int | FAdd | FMul
              | FBranchNZ AnnotateLabel | FJump AnnotateLabel
              | FLabel AnnotateLabel
              deriving (Show)

flatten :: AnnotatedCode -> [FlatCode]
flatten (AAccess _ m c) =
  FAccess m : flatten c
flatten (AFunction _ c bodyLabel e) =
  (FFunction bodyLabel : flatten c) ++ (FLabel bodyLabel : flatten e)
flatten (ASave _ c) =
  FSave : flatten c
flatten (ARestore _ c) =
  FRestore : flatten c
flatten (ACall _ c) =
  FCall : flatten c
flatten (AReturn _) =
  [FReturn]
flatten (AHalt _) =
  [FHalt]
flatten (AConstInt _ n c) =
  FConstInt n : flatten c
flatten (AAdd _ c) =
  FAdd : flatten c
flatten (AMul _ c) =
  FMul : flatten c
flatten (ABranchNZ _ zCode nzLabel nzCode restLabel restCode) =
  [FBranchNZ nzLabel] ++
  flatten zCode ++
  [FLabel nzLabel] ++ flatten nzCode ++
  [FLabel restLabel] ++ flatten restCode
flatten (AJump _ label) =
  [FJump label]

flatSize (FAccess _) = 2
flatSize (FFunction _) = 2
flatSize (FConstInt _) = 2
flatSize (FBranchNZ _) = 2
flatSize (FJump _) = 2
flatSize (FLabel _) = 0
flatSize _ = 1

removeJump :: [FlatCode] -> [FlatCode]
removeJump [] = []
removeJump (FJump dest : FLabel label : cs)
  | dest == label  = FLabel label : removeJump cs
removeJump (c : cs) = c : removeJump cs

tailCall :: [FlatCode] -> [FlatCode]
tailCall [] = []
tailCall (FCall : FReturn : cs) = FTailCall : tailCall cs
tailCall (c : cs) = c : tailCall cs

codeAddress :: [FlatCode] -> [(FlatCode, Word64)]
codeAddress code =
  zip code $ scanl (\offset code -> offset + flatSize code) 0 code

separateEnv :: [(FlatCode, Word64)] -> ([(AnnotateLabel, Word64)], [(FlatCode, Word64)])
separateEnv = (\(a, b) -> (map getLabel a, b)) . partition (isLabel . fst)
  where isLabel (FLabel _) = True
        isLabel _ = False
        getLabel ((FLabel label), addr) = (label, addr)
        getLabel _ = error "getLabel: expected FLabel"

data ByteCode = BAccess Word64 | BFunction Word64 | BSave | BRestore | BCall
              | BReturn | BTailCall | BHalt | BConstInt Int | BAdd | BMul
              | BBranchNZ Word64 | BJump Word64
              deriving (Show)

toByteCode :: [(AnnotateLabel, Word64)] -> [(FlatCode, Word64)] -> [ByteCode]
toByteCode env = map (byteCode env)
  where
    byteCode :: [(AnnotateLabel, Word64)] -> (FlatCode, Word64) -> ByteCode
    byteCode _ ((FAccess m), _) = BAccess m
    byteCode env ((FFunction label), _) = BFunction (getLabel env label)
    byteCode _ (FSave, _) = BSave
    byteCode _ (FRestore, _) = BRestore
    byteCode _ (FCall, _) = BCall
    byteCode _ (FTailCall, _) = BTailCall
    byteCode _ (FReturn, _) = BReturn
    byteCode _ (FHalt, _) = BHalt
    byteCode _ ((FConstInt m), _) = BConstInt m
    byteCode _ (FAdd, _) = BAdd
    byteCode _ (FMul, _) = BMul
    byteCode env ((FBranchNZ label), curr) = BBranchNZ $ (getLabel env label) - curr - 2
    byteCode env ((FJump label), curr) = BJump $ (getLabel env label) - curr - 2

    getLabel :: [(AnnotateLabel, Word64)] -> AnnotateLabel -> Word64
    getLabel table label = maybe (error $ "Unbound label: " ++ show label)
                                 id
                                 (lookup label table)

compile :: Expr -> [ByteCode]
compile expr =
  case typeInfer expr of
    Left str -> error str
    Right _ -> toByteCode env flatCodeAndAddr
  where stages = tailCall . removeJump . flatten . annotate . translate
        makeEnv = separateEnv . codeAddress
        labeledCode = stages expr
        (env, flatCodeAndAddr) = makeEnv labeledCode

showByteCode :: ByteCode -> [Int]
showByteCode (BAccess m) = [1, fromIntegral m]
showByteCode (BFunction addr) = [2, fromIntegral addr]
showByteCode BSave = [3]
showByteCode BRestore = [4]
showByteCode BCall = [5]
showByteCode BTailCall = [6]
showByteCode BReturn = [7]
showByteCode BHalt = [8]
showByteCode (BConstInt n) = [16, n]
showByteCode BAdd = [17]
showByteCode BMul = [18]
showByteCode (BBranchNZ addr) = [32, fromIntegral addr]
showByteCode (BJump addr) = [33, fromIntegral addr]

assemble :: [ByteCode] -> [Int]
assemble = (showByteCode =<<)

printCode :: [ByteCode] -> String
printCode = concat . map (++ "\n") . map showCode
  where showCode :: ByteCode -> String
        showCode (BAccess m) = "    Access " ++ show m
        showCode (BFunction addr) = "    Function " ++ show addr
        showCode BSave = "    Save"
        showCode BRestore = "    Restore"
        showCode BCall = "    Call"
        showCode BTailCall = "    TailCall"
        showCode BReturn = "    Return"
        showCode BHalt = "    Halt"
        showCode (BConstInt n) = "    ConstInt " ++ show n
        showCode BAdd = "    Add"
        showCode BMul = "    Mul"
        showCode (BBranchNZ addr) = "    BranchNZ " ++ show addr
        showCode (BJump addr) = "    Jump " ++ show addr

pY = Lambda "f" (Ap pA pA)
  where pA = Lambda "x" (Ap (Var "f") pXX)
        pXX = Lambda "y" (Ap (Ap (Var "x") (Var "x")) (Var "y"))

pMulF = Lambda "self" $
          Lambda "n" $ Lambda "m" $
            IfZ (Var "n")
              (I 0)
              (Plus (Var "m") (Ap (Ap (Var "self") (Plus (Var "n") (I (-1)))) (Var "m")))

pMul = Fix pMulF

pFactF = Lambda "self" $
            Lambda "n" $
              IfZ (Var "n")
                (I 1)
                (Ap (Ap pMul (Var "n")) (Ap (Var "self") (Plus (Var "n") (I (-1)))))

pFact = Fix pFactF
pFact5 = Ap (Fix pFactF) (I 5)

pLetId = Let "id" (Lambda "x" (Var "x")) $
         Let "idid" (Ap (Var "id") (Var "id")) $
         Ap (Ap p1 (Ap (Var "idid") (I 5))) (Ap (Var "idid") (Var "id"))

tid = translate pid
tzero = translate pzero
tsuc = translate psuc
tadd = translate padd
t1 = translate p1
t2 = translate p2
tflip = translate pflip
tZ515pred = translate pZ515pred
ttest1 = translate ptest1
ttest2 = translate ptest2
ttest3 = translate ptest3
ttest4 = translate ptest4
ttest5 = translate ptest5
ttest6 = translate ptest6
tY = translate pY
tMulF = translate pMulF
tMul = translate pMul
tFactF = translate pFactF
tFact = translate pFact
tFact5 = translate pFact5
tLetId = translate pLetId

cid = compile pid
czero = compile pzero
csuc = compile psuc
cadd = compile padd
c1 = compile p1
c2 = compile p2
cflip = compile pflip
cZ515pred = compile pZ515pred
ctest1 = compile ptest1
ctest2 = compile ptest2
ctest3 = compile ptest3
ctest4 = compile ptest4
ctest5 = compile ptest5
ctest6 = compile ptest6
cY = compile pY
cMulF = compile pMulF
cMul = compile pMul
cFactF = compile pFactF
cFact = compile pFact
cFact5 = compile pFact5
cLetId = compile pLetId

writeAll = do
  let files = [("ctest1", ctest1), ("ctest2", ctest2), ("ctest3", ctest3),
               ("ctest4", ctest4), ("ctest5", ctest5), ("ctest6", ctest6),
               ("cflip", cflip), ("cid", cid), ("czero", czero), ("csuc", csuc),
               ("cadd", cadd), ("c1", c1), ("c2", c2), ("cZ515pred", cZ515pred),
               {-("cY", cY),-} ("cMulF", cMulF), ("cMul", cMul), ("cFactF", cFactF),
               ("cFact", cFact), ("cFact5", cFact5), ("cLetId", cLetId)]
      writeCode code handle = hPutStr handle (printCode code)
      writeAssembled code handle = hPutStr handle (concat $ map (++ "\n") $ map show $ assemble code)
  mapM_ (\(f, c) -> withFile (f ++ "-intr.s") WriteMode (writeCode c)) files
  mapM_ (\(f, c) -> withFile (f ++ "-intr.in") WriteMode (writeAssembled c)) files

cl :: Expr -> String -> IO ()
cl exp filename = do
  let code = assemble $ compile exp
      flatcode = concat $ map (++ "\n") $ map show code
  withFile filename WriteMode $ \ handle ->
    hPutStr handle flatcode

{-

eval' :: [(String, Term)] -> Expr -> (Expr -> Term) -> Term
eval' env (Var x) k = k (variableLookup env x)
eval' env (Lambda x e) k = k (Closure env x e)
eval' env (Ap e1 e2) k =
  eval' env e2 $ \v ->
  eval' env e1 $ \(Closure env' x' e') ->
  eval' ((x',v):env') e' k

eval e = eval' [] e id

-}
