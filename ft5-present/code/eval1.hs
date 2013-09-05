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

eval1 :: Expr -> [(String, Value)] -> Value
eval1 (Var x)    env = lookupEnv env x
eval1 (Lam x e)  env = F env x e
eval1 (Ap e1 e2) env =
  case eval1 e2 env of
    v -> case eval1 e1 env of
           F env' x' e' -> eval1 e' ((x',v):env')
eval1 Zero       env = I 0
eval1 (Suc e)    env =
  case eval1 e env of
    I n -> I (n + 1)
