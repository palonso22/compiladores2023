module Optimizations (optDeclaration) where

import Subst ( subst, closeN)
import Lang
import MonadFD4
import Eval (semOp)
import qualified Data.Map as Map
import Data.ByteString hiding(map, unzip, null, reverse)
import Data.List 
import Encoding
import Common 


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
        
                                                 
                                                 (V _  x, Const _ (CNat n)) -> return $ if n == 0 then (V i x,True) 
                                                                                        else (BinaryOp i op t1' t2',change1 || change2)                                             

                                                 (Const _ (CNat n),V _  x) ->  do printFD4 "3" 
                                                                                  return $ if n == 0 then (V i x,True) 
                                                                                           else (BinaryOp i op t1' t2',change1 || change2)  


                                                 otherwise -> return (t,False)
                                                
                                                                                               

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
                                         return $ (Let i n typ t1' (toScope t2'),change1 || change2)


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
optimizer t = do printFD4 "Optimizando"
                 (t1,change1) <- constantPropagation t
                 (t2,change2) <- constantFolding t1      
                 (t3,change3) <- commonSubexpression t2                          
                 if change1 || change2 || change3 then optimizer t3
                 else return t3


optDeclaration :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optDeclaration (Decl p x t) = do t' <- optimizer t
                                 return $ Decl p x t' 


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
type Depth = Int
type SubExpMap = Map.Map ByteString (TTerm,Int,Depth,Bool)
type TermMap = Map.Map ByteString TTerm

commonSubexpression :: MonadFD4 m => TTerm -> m (TTerm,Bool)
commonSubexpression t = do 
       tm <- findcommonSubexp t Map.empty 0
       let tm1 = Map.filter (\(t,n,_,b) -> n > 1 && not b) tm
       (t',tm2) <- factorizer t tm1
       let ls = Map.toList tm2    
       let ls' = sortBy (\(k1,_) -> \(k2,_) -> let (_,_,d1,_) = case  Map.lookup k1 tm1 of 
                                                                 Just x -> x 
                                                                 _ -> error $ show k1
                                                   (_,_,d2,_) = case  Map.lookup k2 tm1 of 
                                                                 Just x -> x 
                                                                 _ -> error $ show k2
                                               in compare d1 d2)  
                                            ls                              
           ls'' = map (\(k,(t,_,_,_)) -> (show k,t)) ls'
           (names,_) = unzip ls''                           
       return (wrapperLet (closeN (reverse names) t') ls'', not $ null names)                                        


{-
Cuenta cuantas veces una subexpresion se repite y no las cuenta si tienen efectos laterales
-}               
findcommonSubexp:: MonadFD4 m => TTerm -> SubExpMap -> Depth -> m SubExpMap
findcommonSubexp t@(V i v) tm _ = return tm

findcommonSubexp t@(Const i c) tm _ = return tm

findcommonSubexp (Lam _ _ _ t) tm n = findcommonSubexp (fromScope t) tm (n+1)

findcommonSubexp t@(App i t1 t2) tm n = do       
       tm1 <- findcommonSubexp t1 tm (n+1)
       let h1 = hashTerm t1
       tm2 <- findcommonSubexp t2 tm1 (n+1)   
       let h2 = hashTerm t2
       let b = hasLateralEffect h2 tm1 || hasLateralEffect h2 tm2
       countSubexp t b tm2 n      

findcommonSubexp t@(BinaryOp i bo t1 t2) tm n = do
       tm' <- findcommonSubexp t1 tm (n+1)
       let h1 = hashTerm t1
       let b1 = hasLateralEffect h1 tm' 
       tm'' <- findcommonSubexp t2 tm' (n+1)   
       let h2 = hashTerm t2
       let b2 = hasLateralEffect h2 tm'' 
       countSubexp t (b1 || b2) tm'' n      
                      

findcommonSubexp t@(IfZ i tz tt tf) tm n = do
       tm1 <- findcommonSubexp tz tm (n+1)
       let h1 = hashTerm tz
       tm2 <- findcommonSubexp tt tm1 (n+1)   
       let h2 = hashTerm tt
       tm3 <- findcommonSubexp tf tm2 (n+1)
       let h3 = hashTerm tf
       let b = (hasLateralEffect h1 tm3) || (hasLateralEffect h2 tm3) || (hasLateralEffect h3 tm3) 
       countSubexp t b tm3 n      
                      

findcommonSubexp t@(Print _ _ t1) tm n = do
       tm1 <- findcommonSubexp t1 tm (n+1)
       countSubexp t True tm1 n

findcommonSubexp (Fix _ _ _ _ _ t) tm n = findcommonSubexp (fromScope2 t) tm (n+1)

findcommonSubexp t@(Let _ _ _ t1  t2) tm n = do 
       tm1 <- findcommonSubexp t1 tm (n+1)
       let h1 = hashTerm t1
       tm2 <- findcommonSubexp (fromScope t2) tm1 (n+1)
       let h2 = hashTerm (fromScope t2)
       let b = (hasLateralEffect h1 tm2) || (hasLateralEffect h2 tm2)
       countSubexp t b tm2 (n+1)

countSubexp :: MonadFD4 m => TTerm -> Bool -> SubExpMap -> Depth -> m SubExpMap
countSubexp t b tm depth = return $  let h = hashTerm t in
                                     case Map.lookup h tm of 
                                       Nothing -> Map.insert h (t,1,depth,b) tm
                                       Just (_,n,d,_) -> Map.insert h (t,n+1,max depth d,b) tm


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
  | Let info Name Ty (Tm info var)  (Tm info var)
-}
wrapperLet ::  TTerm -> [(String,TTerm)] -> TTerm

wrapperLet t [] = t 

wrapperLet t ((v,trm):xs) = let t' = Let ((Pos 0 0),NatTy) v NatTy trm (toScope t)
                            in wrapperLet t' xs


semInsert ::  ByteString -> TTerm -> SubExpMap -> SubExpMap
semInsert h t m =    case Map.lookup h m of 
                            Just (_,n,d,b) -> Map.insert h (t,n,d,b) m
                            _ -> error "Esto no debería ocurrir"

hasLateralEffect :: ByteString -> SubExpMap -> Bool
hasLateralEffect h m = case Map.lookup h m of 
                         Nothing -> False
                         Just (_,_,_,b) -> b