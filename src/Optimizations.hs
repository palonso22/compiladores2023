module Optimizations (optDeclaration) where

import Subst ( subst, closes)
import MonadFD4
import Lang
import Eval (semOp)
import qualified Data.Map as Map
import Data.ByteString hiding(map, unzip, null, reverse, maximum, partition)
import Data.List
import Encoding
import Common
import PPrint(ppDecl, pp)


bound :: Int
bound = 1000000

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
       ppt3 <- pp t3
       printFD4 ppt3
       -- printFD4 "con esto entro"
       -- ppt <- pp t
       -- printFD4 ppt
       return t3
       -- if change1 || change2 || change3 then optimizer t3
       -- else return t3       
       


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
type MinBound = Int -- Maximo bound en un termino
type RecursiveIndex = Int -- Encuentra terminos recursivos
type Key = (ByteString, Lambdas)
type CommonExpMap = Map.Map Key (TTerm,Int, Depth, Bool, MinBound)
type TermMap = Map.Map ByteString TTerm

commonSubexpression :: MonadFD4 m => TTerm -> m (TTerm,Bool)
commonSubexpression t = do
       (m, t', hc, _) <- findCommonSubExp t Map.empty 0 0 (-1)      
       let (tf, hcf) = factorizer t' m 0
       return (tf, hc || hcf)


getMinBound:: TTerm -> Lambdas -> CommonExpMap -> Int
getMinBound t l m = case Map.lookup (hashTerm t, l) m of
                     Nothing -> getMinBoundTerm t
                     Just (_, _, _,_, mb) -> mb

getMinBoundTerm:: TTerm -> MinBound
getMinBoundTerm (V info (Bound n)) = n
getMinBoundTerm (App i t1 t2) = min (getMinBoundTerm t1) (getMinBoundTerm t2)
getMinBoundTerm _ = bound


countSubexp :: TTerm -> Bool -> CommonExpMap -> Depth -> Lambdas -> MinBound -> CommonExpMap
countSubexp t b m depth l mb =
       let k = (hashTerm t,l) in
              case Map.lookup k m of
                     Nothing -> Map.insert k (t,1,depth,b, mb) m
                     Just (_,n,d,_, mbb) -> Map.insert k (t,n+1,min depth d,b, min mb mbb) m


{- 
Reemplazar expresiones que suceden varias veces por variables libres
Retorna: Termino modificado, Mapa actualizado
-}

replaceExpByHash :: TTerm -> Lambdas -> CommonExpMap -> TTerm

replaceExpByHash t@(V _ _) _ _ =  t

replaceExpByHash t@(Const _ _) _ _ = t

replaceExpByHash  t@(Lam i n ty t1) l m = do
       let t1' = replaceExpByHash (fromScope t1) (l+1) m
       Lam i n ty (toScope t1')

replaceExpByHash t@(App i t1 t2) l m = do
       let h = hashTerm t
       let t1' = replaceExpByHash t1 l m
       let t2' = replaceExpByHash t2 l m
       let app = App i t1' t2'
       case Map.lookup (h,l) m of
              Nothing -> app
              _ -> V i (Free $ show h)--(V i (Free $ show h),replaceExp (h,l) bot m2)

replaceExpByHash t@(Print i s t1) l m = do
       let h = hashTerm t
           t1' = replaceExpByHash t1 l m
       Print i s t1'

replaceExpByHash t@(BinaryOp i bo t1 t2) l m = do
       let h = hashTerm t
       let t1' = replaceExpByHash t1 l m
       let t2' = replaceExpByHash t2 l m
       let bot = BinaryOp i bo t1' t2'
       case Map.lookup (h,l) m of
              Nothing -> bot
              _ -> V i (Free $ show h)

replaceExpByHash t@(IfZ i tz tt tf) l m = do
       let tz' = replaceExpByHash tz l m
           tt' = replaceExpByHash tt l m
           tf' = replaceExpByHash tf l m
       IfZ i tz' tt' tf'

replaceExpByHash  t@(Let i n ty t1 t2) l m = do
       let h = hashTerm t
       let t1' = replaceExpByHash t1 l m
       let t2' = replaceExpByHash (fromScope t2) (l+1) m
       Let i n ty t1' (toScope t2')

replaceExpByHash t@(Fix i n1 ty1 n2 ty2 t1) l m = do
       let t1' = replaceExpByHash (fromScope2 t1) (l+2) m
       Fix i n1 ty1 n2 ty2 (toScope2 t1')

{-
Envolver un término con lets 
-}
--wrapperLet ::  TTerm -> [(String,TTerm, Lambdas, MaxBound)] -> Lambdas -> TTerm

-- wrapperLet t [] _  = t

-- wrapperLet (Lam i n ty t) xs l  = Lam i n ty (toScope (wrapperLet (fromScope t) xs (l+1)))

-- wrapperLet (Fix i n tn v tv t) xs l  = Fix i n tn v tv (toScope2 (wrapperLet (fromScope2 t) xs (l+2) ))

-- wrapperLet (Let i n ty d t) xs l  = Let i n ty d (toScope (wrapperLet (fromScope t) xs (l+1)))

-- wrapperLet t xs l  = let (xs', xs'') = partition (checkOpenVars l) xs
--                          t' = wrapperLet' t xs'
--                      in  wrapperLet t' xs'' l
--        where checkOpenVars ll (_, _, dl, mb) = mb == -1 || mb >= dl - ll

wrapperLet :: TTerm -> [(String,TTerm, Lambdas, MinBound)] -> TTerm
wrapperLet t [] = t
wrapperLet t ((v,trm, _, _):xs) = Let (Pos 0 0, getTy t) v (getTy trm) trm (closes v ( wrapperLet t xs))


-- Devuelve si una expresion posee efectos laterales
hasLateralEffect :: Key -> CommonExpMap -> Bool
hasLateralEffect h m = case Map.lookup h m of
                         Nothing -> False
                         Just (_,_,_,b,_) -> b


checkRecursiveIndex::RecursiveIndex->RecursiveIndex
checkRecursiveIndex (-1) = -1
checkRecursiveIndex ri = ri+1

findCommonSubExp:: MonadFD4 m => TTerm -> CommonExpMap -> Depth -> Lambdas -> RecursiveIndex -> m (CommonExpMap,TTerm, Bool, Bool)
findCommonSubExp t@(V i v) m d l ri = return (countSubexp t False m d l (getMinBoundTerm t), t, False, False)


findCommonSubExp t@(Const i c) m _ _ _ = return (m,t, False, False)

findCommonSubExp (Lam i n ty t) m d l ri = do
       (m1, t', hc, le) <- findCommonSubExp (fromScope t) m (d+1) (l+1) (checkRecursiveIndex ri) 
       let (local, returnMap) = Map.partitionWithKey (\(_,dd) (_,_,_,_, mb) -> mb < bound) m1      
       let (tf, hcf) = factorizer t' local (l+1)
       return (returnMap, Lam i n ty (toScope tf ), hc || hcf, le)


findCommonSubExp t@(App i t1 t2) m d l ri = do              
       (m1, t1', hc1, le1) <- findCommonSubExp t1 m (d+1) l ri
       (m2, t2', hc2, le2) <- findCommonSubExp t2 m1 (d+1) l ri
       let mb1 = getMinBound t1 l m2
       let mb2 = getMinBound t2 l m2
       let localLe = le1 || le2
       -- Analyze recursive expression or lateral effects
       return $ if containsBound ri t1' || localLe then  (m2, App i t1' t2', hc1 || hc2, localLe)
                else (countSubexp t False m2 d l (min mb1 mb2), App i t1' t2', hc1 || hc2, localLe)

   
findCommonSubExp t@(BinaryOp i bo t1 t2) m d l ri = do
       (m1,t1', hc1, le1) <- findCommonSubExp t1 m (d+1) l ri
       (m2,t2', hc2, le2) <- findCommonSubExp t2 m1 (d+1) l ri
       let mb1 = getMinBound t1 l m2
       let mb2 = getMinBound t2 l m2
       let localLe = le1 || le2
       return (countSubexp t False m2 d l (min mb1 mb2), BinaryOp i bo t1' t2', hc1 || hc2, localLe)


findCommonSubExp t@(IfZ i t1 t2 t3) m d l ri = do
       (m1,t1', hc1, le1) <- findCommonSubExp t1 m (d+1) l ri
       (m2,t2', hc2, le2) <- findCommonSubExp t2 m1 (d+1) l ri
       (m3,t3', hc3, le3) <- findCommonSubExp t3 m2 (d+1) l ri
       let localLe = le1 || le2 || le3
       return (m3, IfZ i t1' t2' t3', hc1 || hc2 || hc3, localLe)


findCommonSubExp (Print i s t) m d l ri = do
       (m1,t1', hc, _) <- findCommonSubExp t m (d+1) l ri
       return (m1,Print i s t1', hc, True)

findCommonSubExp (Fix i n1 ty n2 ty2 t) m d l ri = do
       (m1,t', hc, le) <- findCommonSubExp (fromScope2 t) m (d+1) (l+2) 1
       let (local, returnMap) = Map.partitionWithKey (\(_,dd) (_,_,_,_, mb) -> mb < bound) m1       
       let (tf, hcf) = factorizer t' local (l+2)
       return (returnMap,Fix i n1 ty n2 ty2 (toScope2 tf), hc || hcf, le)
      

findCommonSubExp t@(Let i v ty t1  t2) m d l ri = do
       (m1,t1', hc1, le1) <- findCommonSubExp t1 m d l ri
       (m2,t2', hc2, le2) <- findCommonSubExp (fromScope t2) m1 (d+1) (l+1) (checkRecursiveIndex ri)
            
       let (local, returnMap) = Map.partitionWithKey (\(_,dd) (_,_,_,_, mb) -> mb < bound) m2

       let (tf, hcf) = factorizer t2' local (l+1)      
       let localLe = le1 || le2
       return (returnMap, Let i v ty t1' (toScope tf), hc1 || hc2 || hcf, le2)



-- Retorna termino factorizado
factorizer:: TTerm -> CommonExpMap -> Lambdas -> (TTerm, Bool)
factorizer t m l = do

       -- Eliminar expresiones q no se repiten o variables
       let m1 = Map.filter (\(tt,n,_,b, _) -> isNotVar tt && n > 1) m

       -- Reemplazar expresiones repetidas por su hash en el termino
       let t' = replaceExpByHash t l m1

       -- Ordenar terminos por profundidad
       let ls = Map.toList m1
           ls' = sortBy (\ (k1, (_,_,d1, _, _)) (k2, (_,_,d2,_, _)) ->  compare d1 d2) ls
           ls'' = map (\((h,dd),(tt,_,_,_, mb)) -> let nm = show h in  (show h, tt, l, mb)) ls'

       -- Declarar expresiones repetidas
       (wrapperLet t' (reverse ls''), not $ null ls'')


isNotVar::TTerm->Bool
isNotVar (V _ _) = False
isNotVar _ = True


-- Function to check if a bound variable with a specific index exists in the AST
containsBound :: RecursiveIndex -> Tm info Var -> Bool
containsBound (-1) = const False
containsBound n = go 0 -- Start with an initial binding depth of 0
  where
    go (-1) _ = False
    go depth (V _ (Bound m))       = m == n + depth
    go _ (V _ _)                   = False
    go _ (Const _ _)               = False
    go depth (Lam _ _ _ (Sc1 t))   = go (depth + 1) t -- Increment depth in lambda
    go depth (App _ l r)           = go depth l || go depth r
    go depth (Print _ _ t)         = go depth t
    go depth (BinaryOp _ _ t u)    = go depth t || go depth u
    go depth (Fix _ _ _ _ _ (Sc2 t)) = go (depth + 2) t -- Increment depth by 2 in Fix
    go depth (IfZ _ c t e)         = go depth c || go depth t || go depth e
    go depth (Let _ _ _ e (Sc1 t)) = go depth e || go (depth + 1) t -- Increment depth in Let

-- Example of using containsBound
-- You would call this function with an AST to check if a specific bound variable exists
