module Optimizations (optDeclaration) where

import Subst ( subst, close, closes)
import MonadFD4
import Lang
import Eval (semOp)
import qualified Data.Map as Map
import Data.ByteString hiding(map, unzip, null, reverse, maximum, partition)
import Data.List
import Encoding
import Common
import PPrint(ppDecl)
import Data.Bifunctor(second)
import MonadFD4 (printFD4, MonadFD4)
import Data.Foldable (Foldable(toList))
import Data.Binary.Get (isEmpty)


constantFolding:: MonadFD4 m => TTerm -> m (TTerm,Bool)

constantFolding t@(V i v) = return $ (t,False)

constantFolding t@(Const i c) = return $ (t,False)

constantFolding tt@(Lam i n ty t) = do (t',change) <- constantFolding (fromScope t)
                                       return (Lam i n ty (toScope t'),change)

constantFolding tt@(Print i s t) =  do (t',change) <- constantFolding t
                                       return (Print i s t',change)

constantFolding (App i t1 t2) = do (t1',change1) <- constantFolding t1
                                   (t2',change2) <- constantFolding t2
                                   return $ (App i t1' t2',change1 || change2)

constantFolding t@(BinaryOp i op t1 t2) = do (t1',change1) <- constantFolding t1
                                             (t2',change2) <- constantFolding t2
                                             case (t1',t2') of
                                                 (Const _ (CNat n), Const _ (CNat m)) -> return $ (Const i (CNat (semOp op n m)),True)
                                                 otherwise ->return (BinaryOp i op t1' t2',change1 || change2)



constantFolding (Fix i n1 t1 n2 t2 t) = do (t',change) <- constantFolding (fromScope2 t)
                                           return (Fix i n1 t1 n2 t2 (toScope2 t'),change)

constantFolding (IfZ i c t1 t2) = do
                                     (c',change1) <- constantFolding c
                                     case c' of
                                            (Const _ (CNat n)) -> if n == 0 then do (t1',change2) <- constantFolding t1
                                                                                    return (t1',True)
                                                                  else do (t2',change3) <- constantFolding t2
                                                                          return (t2',True)
                                            otherwise -> do (t1',change2) <- constantFolding t1
                                                            (t2',change3) <- constantFolding t2
                                                            return $ (IfZ i c' t1' t2',change1 || change2 || change3)



constantFolding (Let i n typ t1 t2) = do (t1',change1) <- constantFolding t1
                                         (t2',change2) <- constantFolding (fromScope t2)
                                         return (Let i n typ t1' (toScope t2'),change1 || change2)


constantPropagation:: MonadFD4 m => TTerm -> m (TTerm,Bool)
constantPropagation t@(V i v) = return $ (t,False)

constantPropagation t@(Const i c) = return $ (t,False)

constantPropagation tt@(Lam i n ty t) = do (t',change) <- constantPropagation (fromScope t)
                                           return (Lam i n ty (toScope t'),change)

constantPropagation tt@(App i t1 t2) = do (t1', change1) <- constantPropagation t1
                                          (t2', change2) <- constantPropagation t2
                                          return (App i t1' t2', change1 || change2)

constantPropagation tt@(Print i s t) = do (t',change) <- constantPropagation t
                                          return (Print i s t',change)

constantPropagation tt@(BinaryOp i op t1 t2) = do (t1',change1) <- constantPropagation t1
                                                  (t2',change2) <- constantPropagation t2
                                                  return (BinaryOp i op t1' t2', change1 || change2)

constantPropagation (Fix i n1 t1 n2 t2 t) = do (t',change) <- constantPropagation (fromScope2 t)
                                               return (Fix i n1 t1 n2 t2 (toScope2 t'),change)

constantPropagation (IfZ i c t1 t2) = do (c',change1) <- constantPropagation c
                                         (t1', change2) <- constantPropagation t1
                                         (t2', change3) <- constantPropagation t2
                                         return (IfZ i c' t1' t2', change1 || change2 || change3)

constantPropagation tt@(Let i n ty t1 t2) = do
                                               (t1', change1) <- constantPropagation t1
                                               case t1' of
                                                   (Const _ (CNat n')) -> do (t2',change2) <- constantPropagation $ subst t1' t2
                                                                             return  (t2', True)

                                                   _ -> return (Let i n ty t1' t2, change1)

optimizer::MonadFD4 m => TTerm -> m TTerm
optimizer t = do
       printFD4 "Optimizando"
       (t1,change1) <- constantPropagation t
       when change1 (printFD4 "Se aplico constant propagation")
       (t2,change2) <- constantFolding t1
       when change2 (printFD4 "Se aplico constant folding")
       (t3,change3) <- commonSubexpression t2
       when change3 (printFD4 "Se aplico common subexpression")
       when change3 (printFD4 $ show t)
       when change3 (printFD4 $ show t3)
       if change1 || change2 || change3 then optimizer t3
       else return t3


optDeclaration :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optDeclaration (Decl p x t) = do t' <- optimizer t
                                 let decl' = Decl p x t'
                                 ppterm <- ppDecl decl'
                                 --printFD4 "Declaracion optimizada:"
                                 -- printFD4 ppterm
                                 return decl'


{- Contiene:
    - Termino
    - Cantidad de ocurrencias del termino
    - Profundidad del nodo

data Tm info var =
    V info var
  | Const info Const
  | Lam info Name Ty (Tm info var)
  | App info (Tm info var) (Tm info var)
  | Print info String (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | Fix info Name Ty Name Ty (Tm info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var)  (Tm info var)
  
  deriving (Show, Functor)
-}
type Depth = Int -- Cuanto descendimos en el termino
type Lambdas = Int -- Cantidad de lambdas que descendimos en el termino
type MaxBound = Int -- Maximo bound en un termino
type Key = (ByteString, Lambdas)
type SubExpMap = Map.Map Key (TTerm,Int,Depth,Bool, MaxBound)
type TermMap = Map.Map ByteString TTerm

commonSubexpression :: MonadFD4 m => TTerm -> m (TTerm,Bool)
commonSubexpression t = do
       -- Encontrar subexpresiones comunes
       m <- findcommonSubexp t Map.empty 0 0
       -- Filtrar expresiones con efectos laterales o q solo suceden una vez
       let m1 = Map.filter (\(t,n,_,b, _) -> n > 1 && not b) m
       -- Reemplazar operaciones q se repiten por su hash
       (t',m2) <- factorizer t 0 m1
       let ls = Map.toList m2
       -- Ordenar terminos por profundidad
       let ls' = sortBy (\ (k1, (_,_,d1, _, _)) (k2, (_,_,d2,_, _)) ->  compare d1 d2)
                                            ls
           ls'' = map (\((h,l),(t,_,_,_, mb)) -> let nm = show h in  (nm, t, l, mb)) ls'
       -- Envolver en lets
       -- let tt = wrapperLet t' (reverse ls'') 0
       -- printFD4 $ show tt  
       return (wrapperLet t' (reverse ls'') 0  , not $ null ls'')

getMaxBoundVar:: Var -> MaxBound
getMaxBoundVar (Bound n) = n
getMaxBoundVar _ = -1

getMaxBound:: Key -> SubExpMap -> Int
getMaxBound h tm = case Map.lookup h tm of
                     Nothing -> -1
                     Just (_, _, _,_, mb) -> mb

{-
Cuenta cuantas veces una subexpresion se repite y no las cuenta si tienen efectos laterales
-}
findcommonSubexp:: MonadFD4 m => TTerm -> SubExpMap -> Depth -> Lambdas -> m SubExpMap
findcommonSubexp t@(V i v) m d l = countSubexp t False m d l (getMaxBoundVar v)
findcommonSubexp t@(Const i c) tm _ _ = return tm

findcommonSubexp (Lam _ _ _ t) tm d l = findcommonSubexp (fromScope t) tm (d+1) (l+1)

findcommonSubexp t@(App i t1 t2) m d l = do
       m1 <- findcommonSubexp t1 m (d+1) l
       let h1 = hashTerm t1
       let mb1 = getMaxBound (h1,l) m1
       m2 <- findcommonSubexp t2 m1 (d+1) l
       let h2 = hashTerm t2
       let mb2 = getMaxBound (h2,d) m2
       let b = hasLateralEffect (h1,d) m2 || hasLateralEffect (h2,d) m2
       countSubexp t b m2 d l (max mb1 mb2)

findcommonSubexp t@(BinaryOp i bo t1 t2) m d l = do
       tm' <- findcommonSubexp t1 m (d+1) l
       let h1 = hashTerm t1
       let b1 = hasLateralEffect (h1,d) tm'
       let mb1 = getMaxBound (h1,d) tm'
       tm'' <- findcommonSubexp t2 tm' (d+1) l
       let h2 = hashTerm t2
       let b2 = hasLateralEffect (h2,d) tm''
       let mb2 = getMaxBound (h2,d) tm''
       countSubexp t (b1 || b2) tm'' d l (max mb1 mb2)


findcommonSubexp t@(IfZ i tz tt tf) m d l = do
       m1 <- findcommonSubexp tz m (d+1) l
       let h1 = hashTerm tz
       let mb1 = getMaxBound (h1,d) m
       m2 <- findcommonSubexp tt m1 (d+1) l
       let h2 = hashTerm tt
       let mb2 = getMaxBound (h2,d) m2
       m3 <- findcommonSubexp tf m2 (d+1) l
       let h3 = hashTerm tf
       let mb3 = getMaxBound (h3,d) m3
       let b = hasLateralEffect (h1,l) m3 || hasLateralEffect (h2,l) m3 || hasLateralEffect (h3,l) m3
       countSubexp t b m3 d l (maximum [mb1,mb2,mb3])


findcommonSubexp t@(Print _ _ t1) m d l = do
       tm1 <- findcommonSubexp t1 m (d+1) l
       --countSubexp t True tm1 n l fixxx
       return tm1

findcommonSubexp (Fix _ _ _ _ _ t) m d l = findcommonSubexp (fromScope2 t) m (d+1) (l+2)

findcommonSubexp t@(Let _ _ _ t1  t2) m d l = do
       tm1 <- findcommonSubexp t1 m d l
       let h1 = hashTerm t1
       tm2 <- findcommonSubexp (fromScope t2) tm1 (d+1) (l+1)
       let h2 = hashTerm (fromScope t2)
       let b = hasLateralEffect (h1,l) tm2 || hasLateralEffect (h2,l) tm2
       let mb2 = getMaxBound (h2,l) tm2
       countSubexp t b tm2 (d+1) l mb2

countSubexp :: MonadFD4 m => TTerm -> Bool -> SubExpMap -> Depth -> Lambdas -> MaxBound -> m SubExpMap
countSubexp t@(V i v) b m depth l mb = return $ let k = (hashTerm t,l) in Map.insert k (t,1, depth, False, mb) m
countSubexp t@(Const i c) b m depth l mb = return $ let k = (hashTerm t,l) in Map.insert k (t,1, depth, False, mb) m

countSubexp t b tm depth l mb =
       return $  let k = (hashTerm t,l) in
              case Map.lookup k tm of
                     Nothing -> Map.insert k (t,1,depth,b, mb) tm
                     Just (_,n,d,_, mbb) -> Map.insert k (t,n+1,max depth d,b, max mb mbb) tm


{- 
Reemplazar expresiones que suceden varias veces por variables libres
Retorna: Termino modificado
-}

factorizer :: MonadFD4 m => TTerm -> Lambdas -> SubExpMap -> m (TTerm,SubExpMap)

factorizer t@(V _ _) _ m =  return (t,m)

factorizer t@(Const _ _) _ m = return (t,m)

factorizer  t@(Lam i n ty t1) l m = do
       (t1',m') <- factorizer (fromScope t1) (l+1) m
       return (Lam i n ty (toScope t1'),m')

factorizer t@(App i t1 t2) l m = do 
       let h = hashTerm t
       (t1',m1) <- factorizer t1 l m
       (t2',m2) <- factorizer t2 l m1
       let app = App i t1' t2'
       case Map.lookup (h,l) m of
              Nothing -> return (app,m2)
              _ -> return (V i (Free $ show h),replaceExp (h,l) app m2)

factorizer t@(Print i s t1) l m = do 
       let h = hashTerm t
       (t1',tm') <- factorizer t1 l m       
       return (Print i s t1',tm')

factorizer t@(BinaryOp i bo t1 t2) l m = do
       let h = hashTerm t
       (t1',m1) <- factorizer t1 l m
       (t2',m2) <- factorizer t2 l m1
       let bot = BinaryOp i bo t1' t2'
       case Map.lookup (h,l) m2 of
              Nothing -> return (bot,m2)
              _ -> return (V i (Free $ show h),replaceExp (h,l) bot m2)

factorizer t@(IfZ i tz tt tf) l m = do 
       let h = hashTerm t
       (tz',m1) <- factorizer tz l m
       (tt',m2) <- factorizer tt l m1
       (tf',m3) <- factorizer tf l m2
       let ifz = IfZ i tz' tt' tf'
       case Map.lookup (h,l) m3 of
              Nothing -> return (ifz,m3)
              _ -> return (V i (Free $ show h),replaceExp (h,l) ifz m3)

factorizer  t@(Let i n ty t1 t2) l m = do
       let h = hashTerm t
       (t1',m1) <- factorizer t1 l m
       (t2',m2) <- factorizer (fromScope t2) (l+1) m1
       let t' = Let i n ty t1' (toScope t2')
       case Map.lookup (h,l) m of
              Nothing -> return (t',m2)
              _ -> return (V i (Free $ show h), replaceExp (h,l) t' m2)

factorizer t@(Fix i n1 ty1 n2 ty2 t1) l m = do
       (t1',m') <- factorizer (fromScope2 t1) (l+2) m
       return (Fix i n1 ty1 n2 ty2 (toScope2 t1'),m')

{-
Envolver un término con lets 
-}
wrapperLet ::  TTerm -> [(String,TTerm, Lambdas, MaxBound)] -> Lambdas -> TTerm

wrapperLet t [] _  = t

wrapperLet (Lam i n ty t) xs l  = Lam i n ty (toScope (wrapperLet (fromScope t) xs (l+1)))

wrapperLet (Fix i n tn v tv t) xs l  = Fix i n tn v tv (toScope2 (wrapperLet (fromScope2 t) xs (l+2) ))

wrapperLet (Let i n ty d t) xs l  = Let i n ty d (toScope (wrapperLet (fromScope t) xs (l+1)))

wrapperLet t xs l  = let (xs', xs'') = partition (checkOpenVars l) xs
                         t' = wrapperLet' t xs'
                     in  wrapperLet t' xs'' l
       where checkOpenVars l (_, _, dl, mb) = mb == -1 || mb >= dl - l

wrapperLet' :: TTerm -> [(String,TTerm, Lambdas, MaxBound)] -> TTerm
wrapperLet' t [] = t
wrapperLet' t ((v,trm, _, _):xs) = Let (Pos 0 0, getTy t) v (getTy trm) trm (closes v ( wrapperLet' t xs))

replaceExp ::  Key -> TTerm -> SubExpMap -> SubExpMap
replaceExp h t m = case Map.lookup h m of
                     Just (_,n,d,b,mb) -> Map.insert h (t,n,d,b,mb) m
                     _ -> error "Esto no debería ocurrir"


-- Devuelve si una expresion posee efectos laterales
hasLateralEffect :: Key -> SubExpMap -> Bool
hasLateralEffect h m = case Map.lookup h m of
                         Nothing -> False
                         Just (_,_,_,b,_) -> b