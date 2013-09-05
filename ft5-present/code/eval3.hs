data Expr = Var String
          | Lam String Expr
          | Ap Expr Expr
          | Zero
          | Suc Expr
          deriving Show

lookupEnv :: [(String, Value)] -> String -> Value
lookupEnv env x = case lookup x env of
                    Just v  -> v
                    Nothing -> error "Unbound variable"

data Value = F [(String,Value)] String Expr | I Int

eval3 :: Expr -> [(String, Value)] -> Cont -> Value
eval3 (Var x)    env k = apply k (lookupEnv env x)
eval3 (Lam x e)  env k = apply k (F env x e)
eval3 (Ap e1 e2) env k =
  eval3 e2 env (Cont3 env e1 k)


eval3 Zero       env k = apply k (I 0)
eval3 (Suc e)    env k =
  eval3 e env (Cont1 k)

eval e = eval3 e [] Id

data Cont = Id | Cont1 Cont | Cont2 Value Cont 
          | Cont3 [(String,Value)] Expr Cont

apply Id v = v
apply (Cont1 k) (I n) = apply k (I (n + 1))
apply (Cont2 v k) (F env' x' e') =
  eval3 e' ((x',v):env') k
apply (Cont3 env e1 k) v =
  eval3 e1 env (Cont2 v k)
