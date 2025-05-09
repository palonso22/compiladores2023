{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang hiding (Val, Env)
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char
import Subst(close)

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern IFZ      = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern TAILCALL = 16
pattern IFSTOP   = 17

tailCallOpt :: MonadFD4 m => TTerm -> m Bytecode

tailCallOpt (App _ t1 t2) = do bcT1 <- bcc t1
                               bcT2 <- bcc t2
                               return $ bcT1 ++ bcT2 ++ [TAILCALL]

tailCallOpt (IfZ _ z t1 t2) = do bcz <- bcc z
                                 tc1 <- tailCallOpt t1
                                 tc2 <- tailCallOpt t2
                                 return $ [IFZ,length tc1 + 2] ++ bcz ++ [IFSTOP] ++ tc1 ++ [JUMP,length tc2] ++ tc2

tailCallOpt (Let _ _ ty m n) = do bcM <- bcc m
                                  tcN <- tailCallOpt (fromScope n)
                                  return $ bcM ++ [SHIFT] ++ tcN

tailCallOpt t = do bcT <- bcc t
                   return $ bcT ++ [RETURN]


--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V _ (Bound i)) = return [ACCESS,i]
bcc (Const _ (CNat n)) = return [CONST,n]

bcc (Lam _ n ty t) = do
                       bt <- tailCallOpt (fromScope t)
                       -- bt <- bcc (fromScope t) -- para correr runVM descomentar
                       return $ [FUNCTION,length bt + 1] ++ bt ++ [RETURN]

bcc (App _ t1 t2) = do
                bc1 <- bcc t1
                bc2 <- bcc t2
                return $ bc1++bc2++[CALL]

bcc (Print _ s t) = do
                t' <- bcc t
                return $ [PRINT] ++ map ord s ++ [NULL] ++ t' ++ [PRINTN]

bcc (BinaryOp _ op t1 t2) = do
                    bc1 <- bcc t1
                    bc2 <- bcc t2
                    return $ bc1 ++ bc2 ++ [bcOp op]

 where  bcOp Add = ADD
        bcOp Sub = SUB

bcc (IfZ _ z t1 t2) = do
                      bcz <- bcc z
                      bc1 <- bcc t1
                      bc2 <- bcc t2
                      return $ [IFZ,length bc1 + 2] ++ bcz ++ [IFSTOP] ++ bc1 ++ [JUMP,length bc2] ++ bc2

bcc (Let _ _ _ t1 t2) = do
                        bc1 <- bcc t1
                        bc2 <- bcc (fromScope t2)
                        return $ bc1 ++ [SHIFT] ++ bc2 ++ [DROP]

bcc (Fix _ _ _ _ _ t) = do
                        bc1 <- bcc (fromScope2 t)
                        return $ [FUNCTION,length bc1 + 1] ++ bc1 ++ [RETURN, FIX]

bcc t = error $ "Este case no lo vimos " ++ show t


-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule ds = do let t = elabTerm ds
                          do b <- bcc t
                             return $ b ++ [STOP]


-- Construye un término Let a partir de una lista de declaraciones
-- convirtiendo variables globales en libres
-- y cerrando las variables libres en el cuerpo de cada declaracion 

elabTerm :: [Decl TTerm] -> TTerm
elabTerm [] = error "esto no deberia pasar"
elabTerm [Decl pos name body] = body
elabTerm ((Decl pos name body):xs) =
  let letBody =  elabTerm' xs
  in Let (getInfo body) name (getTy body) body (close name letBody)



elabTerm' :: [Decl TTerm] -> TTerm
elabTerm' [] = error "esto no deberia pasar"
elabTerm' [Decl _ _ b] = replaceGlobal b
elabTerm' ((Decl p n b):ds) = let letBody =  close n (elabTerm' ds) in
                              Let (getInfo b) n NatTy (replaceGlobal b) letBody


-- Abrir variables globales
replaceGlobal::TTerm -> TTerm
replaceGlobal = fmap changeGlobal
  where changeGlobal (Global n) = Free n
        changeGlobal v = v


-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename


-- Tipo de datos para la BVM  

type Env = [Val]
type Stack = [Val]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode  deriving Show


printFD42 :: MonadFD4 m => String -> m ()
printFD42 = liftIO . putStr


checkProfAndStack :: MonadFD4 m => Stack -> m a -> Bool -> m a
checkProfAndStack s action hasClousures = do p <- getProf
                                             if p then do maxS <- getMaxStack
                                                          let currentStack = length s in
                                                           when (currentStack > maxS) $ setMaxStack currentStack
                                                          addOp
                                                          if hasClousures then do actual <- getTotalClousures
                                                                                  setTotalClousures (actual + 1)
                                                                                  action                        
                                                          else action 
                                                  else action


runBC :: MonadFD4 m => Bytecode -> m ()
runBC c = runBC' c [] []
              

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m()

runBC' (CONST:n:c) e s = checkProfAndStack (I n:s) (runBC' c e (I n:s)) False

runBC' (ACCESS:i:c) e s = checkProfAndStack (e!!i:s) (runBC' c e (e!!i:s)) False

runBC' (ADD:c) e (I n1:I n2:s) = checkProfAndStack (I (n1+n2) :s)  (runBC' c e (I (n1+n2) :s)) False

runBC' (SUB:c) e (I n1:I n2:s) = do let res = max (n2-n1) 0
                                    checkProfAndStack (I res :s) (runBC' c e (I res :s)) False

runBC' (CALL:c) e (v:Fun ef cf :s)  = checkProfAndStack (RA e c:s) (runBC' cf (v:ef) (RA e c:s)) False

runBC' (TAILCALL:c) e (v:Fun ef cf :s)  = checkProfAndStack s (runBC' cf (v:ef) s) False


runBC' (IFZ:ctos:c) e s  = checkProfAndStack (RA e []:I ctos:s) (runBC' c e (RA e []:I ctos:s)) False

runBC' (IFSTOP:c) _ (I k:RA e _:I ctos:s) | k == 0 = checkProfAndStack s (runBC' c e s) False
                                          | otherwise = checkProfAndStack s (runBC' (drop ctos c) e s) False

runBC' (JUMP:n:c) e s = checkProfAndStack s (runBC' (drop n c) e s) False

runBC' (FUNCTION:ctos:c) e s = checkProfAndStack (Fun e c:s) (runBC' (drop ctos c) e (Fun e c:s)) True

runBC' (RETURN:_) _ (v:RA e c:s) = checkProfAndStack (v:s) (runBC' c e (v:s)) False

runBC' (FIX:c) e (Fun _ cf:s) = do let efix = Fun efix cf:e
                                   checkProfAndStack (Fun efix cf:s) (runBC' c e (Fun efix cf:s)) True


runBC' (PRINTN:c) e q@(I n:s) = do printFD4 $ show n
                                   checkProfAndStack q (runBC' c e q) False

runBC' (PRINT:c) e s = do let (str,c') = decoderStr "" c
                          printFD42 str
                          checkProfAndStack s (runBC'  c' e s) False

  where -- Consume bytecode y va generando el string codificado
        decoderStr :: String -> [Int] -> (String, [Int])
        decoderStr ss (NULL:cs) = (ss,cs)
        decoderStr ss (x:xs) = decoderStr (ss++[chr x]) xs
        decoderStr _ [] = error "Esto no debería pasar"

runBC' (SHIFT:c) e (v:s) = checkProfAndStack s (runBC' c (v:e) s) False

runBC' (DROP:c) (v:e) s = checkProfAndStack s (runBC' c e s) False

runBC' (STOP:_) _ s = checkProfAndStack s (return ()) False

runBC' xs e s = error $ "BC:"++show xs++"\n"++
                        "Entorno:" ++ show e ++ "\n"++
                        "Stack:" ++ show s

