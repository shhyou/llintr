data Expr = Var String
          | Lam String Expr
          | Ap Expr Expr
          | Zero
          | Suc Expr
          deriving Show

data Value = F [(String,Value)] String Code
           | I Int
           deriving Show

data Stack = Env [(String,Value)]
           | Addr Code
           deriving Show

data Code = Halt
          | Access String Code
          | Const0 Code
          | Closure String Code Code
          | Inc Code
          | Save Code
          | Restore Code
          | Apply Code
          | Return
          deriving Show

lookupEnv :: [(String, Value)] -> String -> Value
lookupEnv env x = case lookup x env of
                    Just v  -> v
                    Nothing -> error "Unbound variable"

compile' (Suc e) rest = compile' e (Inc rest)
compile' (Ap e1 e2) rest =
  Save $
  compile' e2 (Restore $
  compile' e1 (Apply rest))
compile' (Var x) rest = Access x rest
compile' Zero    rest = Const0 rest
compile' (Lam x e) rest =
  Closure x (compile' e Return) rest
compile expr = compile' expr Halt

eval :: Code -> [(String, Value)] -> [Value] -> [Stack] -> Value
eval Halt _ [v] [] = v
eval (Const0 c) env vs stk =
  eval c env (I 0 : vs) stk
eval (Closure x e c) env vs stk =
  eval c env (F env x e : vs) stk
eval (Access x c) env vs stk =
  eval c env (lookupEnv env x : vs) stk
eval (Inc c) env (I n : vs) stk =
  eval c env (I (n+1) : vs) stk
eval (Save c) env vs stk =
  eval c env vs (Env env : stk)
eval (Restore c) _ vs (Env env : stk) =
  eval c env vs stk
eval (Apply c) _ (F env x e : v : vs) stk =
  eval e ((x,v):env) vs (Addr c : stk)
eval Return env vs (Addr c : stk) =
  eval c env vs stk

run c = eval c [] [] []

test0 = (Ap (Lam "x" (Suc (Suc (Var "x")))) (Suc Zero))

test1 = (Ap (Ap (Lam "z" (Var "z"))
                (Ap (Lam "x" (Lam "y" (Suc (Var "x"))))
                    (Suc (Suc Zero))))
            Zero)
