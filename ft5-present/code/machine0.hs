lookupEnv :: [(String, Value)] -> String -> Value
lookupEnv env x = case lookup x env of
                    Just v  -> v
                    Nothing -> error "Unbound variable"

data Expr = Var String
          | Lam String Expr
          | Ap Expr Expr
          | Zero
          | Suc Expr
          deriving Show

data Value = F [(String,Value)] String Expr | I Int

data Stack = Halt | Inc Stack | Apply Value Stack 
           | Call [(String,Value)] Expr Stack

execState :: Expr -> [(String, Value)] -> Stack -> Value
execState (Var x)    env k = valState k (lookupEnv env x)
execState (Lam x e)  env k = valState k (F env x e)
execState (Ap e1 e2) env k = execState e2 env (Call env e1 k)
execState Zero       env k = valState k (I 0)
execState (Suc e)    env k = execState e env (Inc k)

valState :: Stack -> Value -> Value
valState Halt            v              = v
valState (Inc k)         (I n)          = valState k (I (n + 1))
valState (Apply v k)     (F env' x' e') = execState e' ((x',v):env') k
valState (Call env e1 k) v              = execState e1 env (Apply v k)

run e = let I n = execState e [] Halt in n
