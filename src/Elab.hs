{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Lang
import Subst
import MonadFD4

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab t = return $ elab' [] t

elab' :: [Name] -> STerm -> Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env
    then  V p (Free v)
    else V p (Global v)

elab' _ (SConst p c) = Const p c

elab' env (SLam p [(v,ty)] t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (SLam p ((v,ty):vars) t) = Lam p v ty (close v (elab' (v:env) (SLam p vars t)))

elab' env (SFix p (f,fty) [(x,xty)] t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
elab' env (SIfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str t) = Print i str (elab' env t)
-- Aplicaciones generales
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)

elab' env (SLet i rec n ls t def body)
  | null ls = Let i n t (elab' env def)  (close n (elab' (n:env) body))

  | not rec = let fun = SLam i ls def
              in Let i n (buildType $ ls ++ [("",t)]) (elab' env fun) (close n (elab' (n:env) body))

  | otherwise = case ls of
                    [(a,ta)] -> let fix = SFix i (n,t) [(a,ta)] def
                                in Let i n (FunTy ta t) (elab' env fix)  (close n (elab' (n:env)  body))

                    (v:vs)->  let fun = SLam i vs def
                              in elab' env $ SLet i rec n [v] (FunTy (buildType vs) t) fun body


elabDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
elabDecl decl = let pos = sdeclPos decl
                    name = sdeclName decl
                    body = sdeclBody decl
                    args = sdeclArgs decl
                    info = sgetInfo body
                    typ  = sdeclType decl
                    rec = sdeclRec decl
                in  case args of
                    [] -> do body' <- elab body
                             return $ Decl pos name body'
                    _ -> if not rec then do let slam = SLam info args body
                                            lam <- elab slam
                                            return $ Decl pos name lam
                         
                         else do  typNoSugar <- desugarTypeList $ (snd $ unzip args) ++ [typ]
                                  let (v,tv) = head args                                     
                                      sfix = SFix pos (name,typNoSugar) args body
                                  fix <- elab sfix
                                  return $ Decl pos name fix   

-- se consideran listas con al menos un argumento
buildType :: [(Name,Ty)] -> Ty
buildType [] = error "buildType: empty list"
buildType [(_,t)] = t
buildType ((_,t):ts) = FunTy t  $ buildType ts


-- desugarea sinonimos de tipo
desugarTypeList :: MonadFD4 m => [Ty] -> m Ty
desugarTypeList [t] = desugarType t
desugarTypeList (t:ts) = do t' <- desugarType t 
                            ts' <- desugarTypeList ts    
                            return $ FunTy t' ts'

--Chequea si un tipo t esta bien definido y lo convierte si usa sinonimos
desugarType::MonadFD4 m => Ty-> m Ty
desugarType NatTy = return NatTy 
desugarType (SinTy n) = do e <- getSinTypEnv
                           let val = lookup n e
                           case val of 
                               Nothing -> failFD4 $ "El tipo "++n++" no esta definido"                                             
                               Just t -> return t
desugarType (FunTy t ty) = do t'<-desugarType t
                              ty'<-desugarType ty
                              return (FunTy t' ty')



