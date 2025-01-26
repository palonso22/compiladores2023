module CEK(search,fromValtoTerm) where

import Lang
import MonadFD4
import Common

checkProfAndContinue :: MonadFD4 m => m a -> m a
checkProfAndContinue action = do p <- getProf
                                 when p addOp
                                 action

search :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search (Print _ s t) e k = checkProfAndContinue $ search t e (FrPrint  s:k)
search q@(BinaryOp _  bo t1 t2) e k = checkProfAndContinue $ search t1 e (FrOpTer e bo t2:k)
search (IfZ _  c t1 t2) e k = checkProfAndContinue $ search c e (FrIf e t1 t2:k)
search (App _ t1 t2) e k = checkProfAndContinue $ search t1 e (FrAp  e t2:k)
search (V _ (Global n)) e k = do
                                mDecl <- lookupCEKDecl n                                
                                case mDecl of
                                    Nothing -> failFD4 $ "Variable "++n++" indefinida"
                                    Just t -> checkProfAndContinue $ destroy t k
search (Let i n ty t1 t2) e k = checkProfAndContinue $ search t1 e (FrLet e (fromScope t2):k)


search (V _ (Bound n)) e k = checkProfAndContinue $ destroy (e!!n) k
search q@(Const _ (CNat c)) e k = checkProfAndContinue $ destroy (N c) k
search (Lam (_, fty)  n ty t) e k = checkProfAndContinue $ destroy (Clos (ClosFun fty e n ty (fromScope t)))  k
search (Fix (_, fty)  f tf x tv t) e k = checkProfAndContinue $ destroy (Clos (ClosFix fty e f tf x tv (fromScope2 t))) k
search t k v = error $ "Esto no lo consideramos "++ show t ++ "," ++ show k++ "," ++ show v


destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v

destroy v@(N c) ((FrPrint  s):k) = do   printFD4 $ s++show c
                                        checkProfAndContinue $ destroy v k

destroy v ((FrOpTer  e bo t2):k)   = checkProfAndContinue $ search t2 e (FrOpVal  bo v:k)

destroy (N  c1)  ((FrOpVal bo (N  c2)):k) = checkProfAndContinue $ destroy (N  (semOp bo c2 c1)) k

destroy (N  c)  ((FrIf  e t1 t2):k) | c == 0 = checkProfAndContinue $ search t1 e k
                                    | otherwise = checkProfAndContinue $ search t2 e k

destroy q@(Clos clos) u@((FrAp e t):k) = checkProfAndContinue $ search t e (FrClos clos:k)

destroy v (FrClos (ClosFun _ e _ _ t):k) = checkProfAndContinue $ search t (v:e) k

destroy v ((FrClos q@(ClosFix _ e _ _ _ _ t)):k) = checkProfAndContinue $ search t (v:Clos q:e) k

destroy v ((FrLet e t):k) = checkProfAndContinue $ search t (v:e) k

destroy q k = error $ "Esto no lo vimos" ++ show q ++ "," ++ show k

-- | Semántica de operadores binarios
semOp :: BinaryOp -> Int -> Int -> Int
semOp Add x y=  x + y
semOp Sub x y = max 0 (x - y)

fromValtoTerm :: Val -> TTerm
fromValtoTerm (N n) = Const (NoPos, NatTy) (CNat n)
fromValtoTerm (Clos q) = fromClostoTerm q
    where   fromClostoTerm (ClosFun fty e x ty t) = Lam (NoPos, fty) x ty (toScope t)
            fromClostoTerm  (ClosFix fty _ f tf x tv t) = Fix (NoPos, fty) f tf x tv (toScope2 t)