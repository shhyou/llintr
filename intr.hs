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
import System.IO -- for writeAll
import Data.Word
import Data.List (elemIndex) -- used in compile'

data Code = Access Word Code
          | Function Code Code
          | Save Code
          | Restore Code
          | Call Code
          | Return
          | Halt

          | ConstInt Int Code
          | Add Code
          | BranchNZ Code Code Code -- the 3rd Code is for compilation usage only
          | Jump Code               -- Jump should only be used in conjunction
                                    -- with BranchNZ (in both branch)

data Value = Closure Env Code
           | IntV Int

type Env = [Value]

type Values = [Value]
type Stack = [Either Code Env]

data Expr = Var String
          | Lambda String Expr
          | Ap Expr Expr
          | I Int
          | Plus Expr Expr
          | IfZ Expr Expr Expr
          deriving Show

type Machine = (Code, Values, Stack, Env)

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
  show (BranchNZ e1 e2 c) = "BranchNZ Z{" ++ show e1 ++ "} NZ{"
                            ++ show e2 ++ "}; " ++ show c
  show (Jump _) = "Jump;"

instance Show Value where
  show (Closure env c) = "(\\ -> " ++ show c ++ ")"
  show (IntV m) = show m

compile' :: [String] -> Expr -> Code -> Code
compile' var (Var x) c = Access (fromIntegral  idx) c
  where idx = maybe (error ("Unbound variable: " ++ x)) id (x `elemIndex` var)
compile' var (Lambda x e) c = Function c (compile' (x:var) e Return)
compile' var (Ap e0 e1) c = Save $
                            compile' var e1 $
                            Restore $
                            compile' var e0 $
                            Save $
                            Call $
                            Restore $
                            c
compile' _ (I n) c = ConstInt n c
compile' var (Plus e1 e2) c = Save $
                              compile' var e2 $
                              Restore $
                              compile' var e1 $
                              Add $
                              c
compile' var (IfZ e0 e1 e2) c = Save $
                                compile' var e0 $
                                Restore $
                                BranchNZ (compile' var e1 (Jump c))
                                         (compile' var e2 (Jump c))
                                         c

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
removeEnv clean (BranchNZ e1 e2 c) k =
  removeEnv clean e1 $ \[e1clean] e1' ->
  removeEnv clean e2 $ \[e2clean] e2' ->
  removeEnv (e1clean && e2clean) c $ \bs rest ->
  k bs (BranchNZ e1' e2' rest)
removeEnv clean (Jump c) k =
  k [clean] (Jump c)

removeEnv _ c k = k [] c

compile e = removeEnv undefined (compile' [] e Halt) (const id)

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
run (Return, vs, (Left c):stk, _:env) =
  run (c, vs, stk, env)
run (Halt, v:_, _, _) = v

run (ConstInt m c, vs, stk, env) =
  run (c, (IntV m):vs, stk, env)
run (Add c, (IntV m2):(IntV m1):vs, stk, env) =
  run (c, (IntV (m1+m2)):vs, stk, env)
run (BranchNZ e1 e2 _, (IntV m):vs, stk, env) =
  run (if m == 0 then e1 else e2, vs, stk, env)
run (Jump c, vs, stk, env) =
  run (c, vs, stk, env)

run _ = error "Undefined state transition"

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

newName :: State Int String
newName = do
  n <- get
  modify (+1)
  return ('L' : show n)

printCode' :: Code -> State Int (String -> String)
printCode' (Save c) = do
  showRest <- printCode' c
  return $ ("    Save\n" ++) . showRest
printCode' (Restore c) = do
  showRest <- printCode' c
  return $ ("    Restore\n" ++) . showRest
printCode' (Call c) = do
  showRest <- printCode' c
  return $ ("    Call\n" ++) . showRest
printCode' Return =
  return ("    Return\n" ++)
printCode' Halt =
  return ("    Halt\n" ++)
printCode' (Access m c) = do
  showRest <- printCode' c
  return $ (("    Access " ++ show m ++ "\n") ++) . showRest
printCode' (Function c e) = do
  bodyLabel <- newName
  showRest <- printCode' c
  showFunction <- printCode' e
  return $ (("    Function " ++ bodyLabel ++ "\n") ++)
           . showRest
           . ((bodyLabel ++ ":\n") ++)
           . showFunction

printCode' (ConstInt m c) = do
  showRest <- printCode' c
  return $ (("    ConstInt " ++ show m ++ "\n") ++) . showRest
printCode' (Add c) = do
  showRest <- printCode' c
  return $ ("    Add\n" ++) . showRest
printCode' (BranchNZ e1 e2 c) = do
  elseLabel <- newName
  fiLabel <- newName
  showIf <- printCode' e1
  showElse <- printCode' e2
  showRest <- printCode' c
  return $ (("    BranchNZ " ++ elseLabel ++ "\n") ++)
           . showIf
           . (("    Jump " ++ fiLabel ++ "\n") ++)
           . ((elseLabel ++ ":\n") ++)
           . showElse
           . ((fiLabel ++ ":\n") ++)
           . showRest
printCode' (Jump _) =
  return id

printCode c = fst (runState (printCode' c) 0) ""

pY = Lambda "f" (Ap pA pA)
  where pA = Lambda "x" (Ap (Var "f") pXX)
        pXX = Lambda "y" (Ap (Ap (Var "x") (Var "x")) (Var "y"))

pMulF = Lambda "self" $
          Lambda "n" $ Lambda "m" $
            IfZ (Var "n")
              (I 0)
              (Plus (Var "m") (Ap (Ap (Var "self") (Plus (Var "n") (I (-1)))) (Var "m")))

pMul = Ap pY pMulF

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

writeAll = do
  let files = [("ctest1", ctest1), ("ctest2", ctest2), ("ctest3", ctest3),
               ("ctest4", ctest4), ("ctest5", ctest5), ("ctest6", ctest6),
               ("cflip", cflip), ("cid", cid), ("czero", czero), ("csuc", csuc),
               ("cadd", cadd), ("c1", c1), ("c2", c2), ("cZ515pred", cZ515pred),
               ("cY", cY), ("cMulF", cMulF), ("cMul", cMul)]
      writeCode code handle = hPutStr handle (printCode code)
  mapM_ (\(f, c) -> withFile (f ++ "-intr.s") WriteMode (writeCode c)) files

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
