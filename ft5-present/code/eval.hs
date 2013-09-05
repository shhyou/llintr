data Expr = Var String
          | Lam String Expr
          | Ap Expr Expr
          | Zero
          | Suc Expr
          deriving Show

data Value = F (Value -> Value)
           | I Int

lookupEnv :: [(String, Value)] -> String -> Value
lookupEnv env x = case lookup x env of
                    Just v  -> v
                    Nothing -> error "Unbound variable"

eval0 :: Expr -> [(String, Value)] -> Value
eval0 (Var x)    env = lookupEnv env x
eval0 (Lam x e)  env = F (\v -> eval0 e ((x,v):env))
eval0 (Ap e1 e2) env =
  case eval0 e2 env of
    v -> case eval0 e1 env of
           F f -> f v
eval0 Zero       env = I 0
eval0 (Suc e)    env =
  case eval0 e env of
    I n -> I (n + 1)
