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

eval2 :: Expr -> [(String, Value)] -> (Value->Value)->Value
eval2 (Var x)    env k = k (lookupEnv env x)
eval2 (Lam x e)  env k = k (F env x e)
eval2 (Ap e1 e2) env k =
  eval2 e2 env (\v ->
              eval2 e1 env (\(F env' x' e') ->
                           eval2 e' ((x',v):env') k))
eval2 Zero       env k = k (I 0)
eval2 (Suc e)    env k =
       eval2 e env (\(I n)->
           k (I (n + 1)))

eval e = eval2 e [] id
