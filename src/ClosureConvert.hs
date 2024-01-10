module ClosureConvert where

import IR
import Lang
import Control.Monad.Trans.State.Lazy
import Control.Monad.Writer.Lazy
import Subst(open,openN)


type ClosureState a = StateT Int (Writer [IrDecl]) a

closureConvert :: TTerm -> String -> [(Name,Ty)] -> [Name]  -> ClosureState Ir

closureConvert (V (_,ty) v) f xs fwa =
      if  not $ isFun ty then case v of
                                Global s -> return $ IrGlobal ty s
                                Free s -> return $ IrVar ty s

      else case v of
            Global f -> if not $ f `elem` fwa then return $ MkClosure ty f []
                        else return $ IrCall ty (IrVar ty f) [MkClosure ty f [],IrConst (CNat 0)]

            Free f -> return $ IrVar ty (f ++ "_clo")



closureConvert (BinaryOp ty op t1 t2) f xs fwa = do
      ir1 <- closureConvert t1 f xs fwa
      ir2 <- closureConvert t2 f xs fwa
      return $  IrBinaryOp op ir1 ir2

closureConvert (IfZ (_,ty) tz tt tf) f xs fwa = do
      ir1 <- closureConvert tz f xs fwa
      ir2 <- closureConvert tt f xs fwa
      ir3 <- closureConvert tf f xs fwa
      return $ IrIfZ ty ir1 ir2 ir3

closureConvert (Let ty2 x ty1 t1  t2) f xs fwa = do
      let tt = open x t2
      ir1 <- closureConvert t1 f xs fwa

      -- si x es una funcion, se declara su clausura
      -- y se obtiene x a partir de la misma  
      -- ademas la clausura pasa a ser una variable libre en 
      -- los terminos anidados

      let xs' = let xClo = x ++ "_clo" in
                 case ty1 of
                    FunTy _ _ -> (xClo,ClosureTy) : xs
                    _ -> xs

      ir2 <- closureConvert tt f ((x,ty1):xs') fwa
      return $ case ir1 of
                   MkClosure _  x' _ -> let xClo = x ++ "_clo" in
                                        IrLet ClosureTy xClo ir1 (getTypeIr ir2) $
                                        IrLet ty1 x (IrAccess (IrVar ClosureTy xClo) 0) (getTypeIr ir2) ir2

                   _ ->  IrLet (getTypeIr ir1) x ir1 (getTypeIr ir2) ir2



closureConvert t@(Lam (_,typ) x ty t1) f xs fwa = do
      let tt = open x t1
      ns <- freshen [f]
      let name = head ns
          ret = getCod typ

          -- si el argumento es una funcion se 
          -- necesita agregar la clausura de la misma como variable libre 
          -- en los terminos anidados para que estos accedan a la funcion 
          -- usando la clausura

          xs' = let xClo = x ++ "_clo" in
                case ty of
                    FunTy _ _ -> (xClo,ClosureTy) : xs
                    _ -> xs
      irt <- closureConvert tt f ((x,ty):xs') fwa

      -- en caso de que el argumento sea una funcion lo reemplazamos por una clausura
      -- y obtenemos la funcion desde la clausura

      let  (irt', x', ty') = case ty of

                         FunTy _ _ -> let xClo = x ++ "_clo" in
                                      (IrLet ty x  (IrAccess (IrVar ClosureTy xClo) 0 ) (getTypeIr irt) irt, xClo, ClosureTy)

                         _ -> (irt,x,ty)

           decl = IrFun name ret [("clo",ClosureTy),(x', ty')] (declareFreeVars (getTypeIr irt') irt' "clo" $ reverse xs)

      tell [decl]

      return $ MkClosure typ name [IrVar ty x | (x,ty) <- xs]

closureConvert (Fix (_, retTy) ff tf x tv t) f xs fwa = do
      let tt = openN [ff,x] (fromScope2 t)
      let fClo = ff ++ "_clo"
      irt <- closureConvert tt ff ([(ff,tf), (x,tv),(fClo,ClosureTy)] ++ xs) fwa
      let decl = IrFun ff retTy [(fClo,ClosureTy),(x,tv)] (declareFreeVars (getTypeIr irt) irt fClo $ reverse xs)
      tell [decl]
      return $ MkClosure tf ff [IrVar t x | (x,t) <- xs]

closureConvert (App _ t1 t2) f xs fwa = do
      ir2 <- closureConvert t2 f xs fwa
      ir1 <- closureConvert t1 f xs fwa


      case ir1 of
            c@(MkClosure ty n xss)  -> do ns <- freshen ["clo","var"]
                                          let cod = getCod ty
                                          return $ IrCall cod (IrVar ty n) [c,ir2]

            (IrVar ty n) ->  do let fname = reverse $ drop 4 $ reverse n
                                return $ IrCall (getCod ty) (IrVar ty fname) [IrVar ClosureTy n, ir2]

            c@(IrCall ty n args) -> do  ns <- freshen ["clo","var"]
                                        let cloname = ns !! 0
                                            varname = ns !! 1
                                            clovar =  IrVar ClosureTy cloname
                                            retTy = getCod ty
                                        return $ IrLet ClosureTy cloname c retTy $
                                                 IrLet ty varname  (IrAccess clovar  0) retTy $
                                                 IrCall retTy (IrVar ty varname) [clovar,ir2]


            t -> do let tyT = getTypeIr t
                    ns <- freshen ["clo","var"]
                    let tyt = ClosureTy
                        cloname = head ns
                        varname = ns !! 1
                        tyRet = getCod tyT
                        clovar = IrVar ClosureTy cloname
                    return $ IrLet ClosureTy cloname t tyRet  $
                             IrLet tyT varname (IrAccess clovar 0) tyRet $
                             IrCall tyRet (IrVar tyT varname) [clovar,ir2]


closureConvert (Print _ s t) f xs fwa = closureConvert t f xs fwa >>= \ir -> return $ IrPrint s ir

closureConvert (Const _ c) f xs fwa = return $ IrConst c

closureConvert t _ _ _ = errorCase t


errorCase t = error $ "No consideramos este caso " ++ show t

-- Dado un ir y el nombre de la variable donde se almacena la clausura
-- declara todas las variables libre en t

declareFreeVars :: Ty -> Ir -> Name -> [(Name,Ty)] -> Ir

declareFreeVars = declareFreeVars' []
declareFreeVars' _ _ t _ [] = t
declareFreeVars' ys tBody t clo q@((x,ty):xs) =
                                let declaredVars = x : ys in
                                case ty of

                                       (FunTy _ _) -> let xClo = x ++ "_clo" in
                                                      if xClo `elem` ys then IrLet ty x (IrAccess (IrVar ClosureTy xClo) 0) tBody $ declareFreeVars' declaredVars tBody t clo xs

                                                      else IrLet ClosureTy xClo (IrAccess (IrVar ClosureTy clo) (length q)) tBody
                                                           (IrLet ty x (IrAccess (IrVar ClosureTy xClo) 0) tBody $ declareFreeVars' declaredVars tBody t clo xs)




                                       _ -> IrLet ty x (IrAccess (IrVar ClosureTy clo) (length q)) tBody $ declareFreeVars' declaredVars tBody t clo xs




freshen :: [Name] -> ClosureState [Name]
freshen ns = do i <- get
                put $ i + 1
                return $ map (\n -> "__" ++ n ++ show i) ns

getClosureName :: Int -> Name
getClosureName n = "clo" ++ show n


-- declaracion
-- es un valor? 
-- si tiene primer argumento le damos el nombre y el tipo
-- una lista de funciones sin argumentos explicitos
fromStateToList :: Decl TTerm -> Bool -> (Name, Ty) -> [Name] -> [IrDecl]
fromStateToList d isVal fstArg fwa =
  let dName = declName d
      (term, freeVars, ret) = case declBody d of
                               Lam (_,ty) var tv t -> (open var t,[(var,tv)], getCod ty)
                               Fix (_,ty) ff tf var tv t -> (openN [ff,var] (fromScope2 t),[(ff,tf),(var,tv),(dName ++ "_clo",ClosureTy)],getCod ty)
                               t -> (t,[],getTy t)
      irt = closureConvert term dName freeVars fwa
      declArg = if fst fstArg == "" then ("dummy", NatTy) else fstArg
      ((tf,_),decls) = runWriter $ runStateT irt 0
  in if isVal then decls ++ [IrVal dName tf]
     else decls ++ [IrFun dName ret [(dName ++ "_clo",ClosureTy),declArg] tf]


getCod :: Ty -> Ty
getCod (FunTy _ c) = c
getCod _ = error "Esta variable no representa una funcion"

isFun :: Ty -> Bool
isFun (FunTy _ _) = True
isFun _ = False