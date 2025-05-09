{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
                        -- Este parámetro puede cambiar durante la ejecución:
                        -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,      -- ^ Último archivo cargado.
  maxStack :: Int,      -- ^ Máxima cantidad de elementos en la pila
  cantDecl :: Int,      -- ^ Cantidad de declaraciones desde la última carga
  cantOp :: Int,        -- ^ Cantidad de operaciones
  totalClousures :: Int,  -- ^ Cantidad de closures creados
  glb :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  tySin :: [(Name,Ty)],    -- ^ Entorno de sinonimos de tipo
  glbCEK :: [Decl Val]
}

-- ^ Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map (\(Decl _ n b) -> (n, getTy b))  (glb g) ++ map (\(Decl _ n b) -> (n, getTyCEK b))  (glbCEK g)

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval  
  | InteractiveCEK
  | Bytecompile
  | RunVM
  | CC
  -- | Canon
  -- | Assembler
  -- | Build
  deriving (Show, Eq)

data Conf = Conf {
    opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
    prof :: Bool,         --  ^ True, si se debe generar código para mostrar metricas.
    modo :: Mode
}

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 0 0 0 [] [] []
