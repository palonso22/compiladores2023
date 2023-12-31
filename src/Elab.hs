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

module Elab ( elab, elabDecl, desugarType) where

import Lang
import Subst
import MonadFD4

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab t = elab' [] t

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.

  if v `elem` env then  return $ V p (Free v)
                        else return $ V p (Global v)

elab' _ (SConst p c) = return $ Const p c

elab' env (SLam p [(v,st)] t) = do ty <- desugarType st
                                   t' <- elab' (v:env) t
                                   return $ Lam p v ty (close v t')

elab' env (SLam p ((v,st):vars) t) = do ty <- desugarType st
                                        t' <- elab' (v:env) (SLam p vars t)
                                        return $ Lam p v ty (close v t')

elab' env (SFix p (f,sfty) ((x,sxty):vs) t) = do
                          fty <- desugarType sfty
                          xty <- desugarType sxty
                          if null vs then do t' <- elab' (x:f:env) t
                                             return $ Fix p f fty x xty (close2 f x t')
                          else do let slam = SLam p vs t 
                                  slam' <- elab' (f:x:env) slam 
                                  return $ Fix p f fty x xty (close2 f x slam')


elab' env (SIfZ p c t e)         = do
                         c' <- elab' env c
                         t' <- elab' env t
                         e' <- elab' env e
                         return $ IfZ p c' t' e'
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do
                          t' <- elab' env t
                          u' <- elab' env u
                          return $ BinaryOp i o t' u'
-- Operador Print
elab' env (SPrint i str t) = do
                      t' <- elab' env t
                      return $ Print i str t'
-- Aplicaciones generales
elab' env (SApp p h a) = do
                      h' <- elab' env h
                      a' <- elab' env a
                      return $ App p h' a'

elab' env (SLet i rec n ls tr def body)
  | null ls = do
            def' <- elab' env def
            body' <- elab' (n:env) body
            tr' <- desugarType tr
            return $ Let i n tr' def'  (close n body')

  | not rec = let fun = SLam i ls def
              in do fun' <- elab' env fun
                    body' <- elab' (n:env) body
                    fulltype <- desugarTypeList $ map snd ls ++ [tr]
                    return $ Let i n fulltype fun' (close n body')

  | otherwise = do let (v, tv) = head ls
                   tv' <- desugarType tv
                   fulltype <- desugarTypeList $ map snd ls ++ [tr]
                   let sfix = SFix i (n,fulltype) ls def
                   sfix' <- elab' env sfix
                   body' <- elab' (n:v:env) body
                   let Sc2 cbody' = close2 n v body'
                   return $ Let i n fulltype sfix' (Sc1 cbody')


elab' _ e = error $ "Unexpected" ++ show e                   

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

                         else do  typNoSugar <- desugarTypeList $ map snd args ++ [typ]
                                  let (v,tv) = head args
                                      sfix = SFix pos (name,typNoSugar) args body
                                  sfix' <- elab sfix
                                  return $ Decl pos name sfix'

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



