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
                                            (Const _ (CNat n)) -> do printFD4 "4"
                                                                     if n == 0 then do (t1',change2) <- constantFolding t1
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
       if change1 || change2 || change3 then optimizer t3
       else return t3


optDeclaration :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optDeclaration (Decl p x t) = do t' <- optimizer t
                                 let decl' = Decl p x t'
                                 ppterm <- ppDecl decl'
                                 printFD4 "Declaracion optimizada:"
                                 printFD4 ppterm
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
type SubExpMap = Map.Map ByteString (TTerm,Int,Depth,Bool,Lambdas, MaxBound)
type TermMap = Map.Map ByteString TTerm

commonSubexpression :: MonadFD4 m => TTerm -> m (TTerm,Bool)
commonSubexpression t = do
       tm <- findcommonSubexp t Map.empty 0 0       
       let tm1 = Map.filter (\(t,n,_,b,_, _) -> n > 1 && not b) tm
       (t',tm2) <- factorizer t tm1
       let ls = Map.toList tm2      
       -- Ordenar terminos por profundidad
       let ls' = sortBy (\ (k1, _) (k2, _) -> let (_,_,d1,_, _, _) = case  Map.lookup k1 tm1 of
                                                                      Just x -> x
                                                                      _ -> error $ show k1
                                                  (_,_,d2,_,_, _) = case  Map.lookup k2 tm1 of
                                                                      Just x -> x
                                                                      _ -> error $ show k2
                                              in compare d1 d2)
                                            ls
           ls'' = map (\(k,(t,_,_,_,l, mb)) -> let nm = show k in  (nm, t, l, mb)) ls'
       return (wrapperLet t' (reverse ls'') 0  , not $ null ls'')

getMaxBoundVar:: Var -> MaxBound
getMaxBoundVar (Bound n) = n
getMaxBoundVar _ = -1

getMaxBound:: ByteString -> SubExpMap -> Int
getMaxBound h tm = case Map.lookup h tm of
                     Nothing -> -1
                     Just (_, _, _,_, _, mb) -> mb

{-
Cuenta cuantas veces una subexpresion se repite y no las cuenta si tienen efectos laterales
-}
findcommonSubexp:: MonadFD4 m => TTerm -> SubExpMap -> Depth -> Lambdas -> m SubExpMap
findcommonSubexp t@(V i v) tm n l = countSubexp t False tm n l (getMaxBoundVar v)
findcommonSubexp t@(Const i c) tm _ _ = return tm

findcommonSubexp (Lam _ _ _ t) tm n l = findcommonSubexp (fromScope t) tm (n+1) (l+1)

findcommonSubexp t@(App i t1 t2) tm n l = do
       tm1 <- findcommonSubexp t1 tm (n+1) l
       let h1 = hashTerm t1
       let mb1 = getMaxBound h1 tm1
       tm2 <- findcommonSubexp t2 tm1 (n+1) l
       let h2 = hashTerm t2
       let mb2 = getMaxBound h2 tm2
       let b = hasLateralEffect h2 tm1 || hasLateralEffect h2 tm2
       countSubexp t b tm2 n l (max mb1 mb2)

findcommonSubexp t@(BinaryOp i bo t1 t2) tm n l = do
       tm' <- findcommonSubexp t1 tm (n+1) l
       let h1 = hashTerm t1
       let b1 = hasLateralEffect h1 tm'
       let mb1 = getMaxBound h1 tm'      
       tm'' <- findcommonSubexp t2 tm' (n+1) l
       let h2 = hashTerm t2
       let b2 = hasLateralEffect h2 tm''
       let mb2 = getMaxBound h2 tm''    
       countSubexp t (b1 || b2) tm'' n l (max mb1 mb2)


findcommonSubexp t@(IfZ i tz tt tf) tm n l = do
       tm1 <- findcommonSubexp tz tm (n+1) l
       let h1 = hashTerm tz
       let mb1 = getMaxBound h1 tm1
       tm2 <- findcommonSubexp tt tm1 (n+1) l
       let h2 = hashTerm tt
       let mb2 = getMaxBound h2 tm2
       tm3 <- findcommonSubexp tf tm2 (n+1) l
       let h3 = hashTerm tf
       let mb3 = getMaxBound h3 tm3
       let b = hasLateralEffect h1 tm3 || hasLateralEffect h2 tm3 || hasLateralEffect h3 tm3
       countSubexp t b tm3 n l (maximum [mb1,mb2,mb3])


findcommonSubexp t@(Print _ _ t1) tm n l = do
       tm1 <- findcommonSubexp t1 tm (n+1) l
       --countSubexp t True tm1 n l
       return tm1

findcommonSubexp (Fix _ _ _ _ _ t) tm n l = findcommonSubexp (fromScope2 t) tm (n+1) (l+2)

findcommonSubexp t@(Let _ _ _ t1  t2) tm n l = do
       tm1 <- findcommonSubexp t1 tm (n+1) l
       let h1 = hashTerm t1
       tm2 <- findcommonSubexp (fromScope t2) tm1 (n+1) (l+1)
       let h2 = hashTerm (fromScope t2)
       let b = hasLateralEffect h1 tm2 || hasLateralEffect h2 tm2
       let mb2 = getMaxBound h2 tm2
       countSubexp t b tm2 (n+1) l mb2

countSubexp :: MonadFD4 m => TTerm -> Bool -> SubExpMap -> Depth -> Lambdas -> MaxBound -> m SubExpMap
countSubexp t@(V i v) b tm depth l mb = return $ let h = hashTerm t in Map.insert h (t,1, depth, False, l, mb) tm
countSubexp t@(Const i c) b tm depth l mb = return $ let h = hashTerm t in Map.insert h (t,1, depth, False, l, mb) tm

countSubexp t b tm depth l mb =
       return $  let h = hashTerm t in
              case Map.lookup h tm of
                     Nothing -> Map.insert h (t,1,depth,b, l, mb) tm
                     Just (_,n,d,_, ll, mb) -> Map.insert h (t,n+1,max depth d,b,max l ll, mb) tm


{- 
Reemplazar expresiones que suceden varias veces por variables libres
-}

factorizer :: MonadFD4 m => TTerm -> SubExpMap -> m (TTerm,SubExpMap)

factorizer t@(V _ _) tm =  return (t,tm)

factorizer t@(Const _ _) tm = return (t,tm)

factorizer  t@(Lam i n ty t1) tm = do
       (t1',tm') <- factorizer (fromScope t1) tm
       return (Lam i n ty (toScope t1'),tm')

factorizer t@(App i t1 t2) tm = do let h = hashTerm t
                                   (t1',tm1) <- factorizer t1 tm
                                   (t2',tm2) <- factorizer t2 tm1
                                   let app = App i t1' t2'
                                   case Map.lookup h tm of
                                          Nothing -> return (app,tm2)
                                          _ -> return (V i (Free $ show h),semInsert h app tm2)


factorizer t@(Print i s t1) tm = do let h = hashTerm t
                                    (t1',tm') <- factorizer t1 tm
                                    let print = Print i s t1'
                                    return (print,tm')

factorizer t@(BinaryOp i bo t1 t2) tm = do
       let h = hashTerm t
       (t1',tm1) <- factorizer t1 tm
       (t2',tm2) <- factorizer t2 tm1
       let bot = BinaryOp i bo t1' t2'
       case Map.lookup h tm2 of
              Nothing -> return (bot,tm2)
              _ -> return (V i (Free $ show h),semInsert h bot tm2)

factorizer t@(IfZ i tz tt tf) tm = do let h = hashTerm t
                                      (tz',tm1) <- factorizer tz tm
                                      (tt',tm2) <- factorizer tt tm1
                                      (tf',tm3) <- factorizer tf tm2
                                      let ifz = IfZ i tz' tt' tf'
                                      case Map.lookup h tm3 of
                                              Nothing -> return (ifz,tm3)
                                              _ -> return (V i (Free $ show h),semInsert h ifz tm3)

factorizer  t@(Let i n ty t1 t2) tm = do
       let h = hashTerm t
       (t1',tm1) <- factorizer t1 tm
       (t2',tm2) <- factorizer (fromScope t2) tm1
       let t' = Let i n ty t1' (toScope t2')
       case Map.lookup h tm of
              Nothing -> return (t',tm2)
              _ -> return (V i (Free $ show h), semInsert h t' tm2)

factorizer t@(Fix i n1 ty1 n2 ty2 t1) tm = do
       (t1',tm') <- factorizer (fromScope2 t1) tm
       return (Fix i n1 ty1 n2 ty2 (toScope2 t1'),tm')

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

semInsert ::  ByteString -> TTerm -> SubExpMap -> SubExpMap
semInsert h t m =    case Map.lookup h m of
                            Just (_,n,d,b,l,mb) -> Map.insert h (t,n,d,b,l,mb) m
                            _ -> error "Esto no debería ocurrir"

hasLateralEffect :: ByteString -> SubExpMap -> Bool
hasLateralEffect h m = case Map.lookup h m of
                         Nothing -> False
                         Just (_,_,_,b,_,_) -> b