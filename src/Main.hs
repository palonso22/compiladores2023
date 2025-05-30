{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe )

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabDecl, desugarType, desugarTypeList)
import Eval ( eval )
import PPrint ( pp , ppTy, ppDecl )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import CEK(search)
import Optimizations
import Bytecompile(bytecompileModule, bcWrite, bcRead, runBC)
import Data.List.Split (endBy)
import IR
import ClosureConvert(fromStateToList)
import C(ir2C)
import Data.Maybe (fromJust,isJust)

prompt :: String
prompt = "FD4> "



-- | Parser de banderas
parseMode :: Parser (Mode,Bool,Bool)
parseMode = (,,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval        Eval        (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' Assembler ( long "assembler" <> short 'a' <> help "Imprimir Assembler resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
   -- <*> pure False
   -- reemplazar por la siguiente línea para habilitar opción
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")
   <*> flag False True (long "profile" <> short 'p' <> help "Muestra metricas sobre la ejecución")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool,Bool, [FilePath])
parseArgs = (\(a,b,c) d -> (a,b,c,d)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2022" )

    go :: (Mode,Bool,Bool,[FilePath]) -> IO ()
    go (Interactive,opt,prof,files) =
              runOrFail (Conf opt prof Interactive) (runInputT defaultSettings (repl files))
    go (RunVM, opt,prof,files) =
               runOrFail (Conf opt prof RunVM) $ mapM_ bytecodeRun files
    go (m,opt,prof, files) =
              runOrFail (Conf opt prof m) $ mapM_ compileFile files

runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compileFile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl STerm]
loadFile f = do
    let filename = reverse (dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mode <- getMode
    mapM_ handleDecl decls
    setInter i
    let [fs] = endBy ".fd4" f
    when (mode == Bytecompile) (bytecompileFile fs decls)
    when (mode == CC) (ccFile fs decls)


ccFile :: MonadFD4 m => FilePath -> [SDecl STerm] -> m()
ccFile f sdecls = do
  let sdecls' = filter isDecl sdecls -- Eliminar sinomimos de tipo
      ns = map sdeclName sdecls'
  decls <- mapM lookDecls ns
  -- mapear cada declaracion con su tipo y su primer argumento si lo tiene                  
  info <- mapM (\d -> let args = unzip $ sdeclArgs d
                          argsTypes = snd args
                          argsName = fst args
                          firstArg = if null argsName then ""
                                    else head argsName in
                          desugarTypeList (argsTypes ++ [sdeclType d]) >>= \t ->

                      return (sdeclName d, (checkIsVal t, (firstArg, firstArgType t)))) sdecls'

  -- definir que declaraciones representan funciones sin argumentos explicitos
  let declsWithoutArgs = filter (\d -> let infoDecl = fromJust (lookup (sdeclName d) info) in
                                      not (fst infoDecl) && (fst.snd) infoDecl == "")  sdecls'

      funcNamesWithoutArgs = map sdeclName declsWithoutArgs

      irDecls = concatMap (\d ->  let infoDecl = fromJust $ lookup (declName d) info in
                               uncurry (fromStateToList d) infoDecl funcNamesWithoutArgs) decls

  liftIO $ writeFile (f ++ ".c") (ir2C (IrDecls irDecls))


bytecompileFile :: MonadFD4 m => FilePath -> [SDecl STerm] -> m ()
bytecompileFile f sdecls = do
            let ns = map sdeclName $ filter isDecl sdecls -- Eliminar sinomimos de tipo
            decls <- mapM lookDecls ns
            bc <- bytecompileModule decls
            liftIO $ bcWrite bc $ f ++ ".bc32"



lookDecls :: MonadFD4 m => Name -> m (Decl TTerm)
lookDecls n = do  m <- lookupDecl2 n
                  case m of
                    Just d -> return d
                    Nothing -> error "esto no deberia pasar"


isDecl:: SDecl a -> Bool
isDecl (SDecl {}) = True
isDecl _ = False

bytecodeRun :: MonadFD4 m => FilePath -> m()
bytecodeRun filePath = liftIO (bcRead filePath) >>= \bc -> do runBC bc
                                                              p <- getProf
                                                              if p then do getOp >>= printFD4 . ("Cantidad de operaciones: "++) . show else return ()
                                                              if p then do getMaxStack >>= printFD4 . ("Tamaño maximo del stack: "++) . show else return ()
                                                              if p then do getTotalClousures >>= printFD4 . ("Cantidad de clousures: "++) . show else return ()

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

evalDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDecl (Decl p x e) = do
    e' <- eval e
    return (Decl p x e')

evalCEKDecl :: MonadFD4 m => Decl TTerm -> m (Decl Val)
evalCEKDecl (Decl p x e) = do
    e' <- search e [] []
    return (Decl p x e')


handleDecl ::  MonadFD4 m => SDecl STerm -> m ()
handleDecl sd@SDecl {} = do
        m <- getMode
        case m of
          Interactive -> do
              (Decl p x tt) <- typecheckDecl sd
              te <- eval tt
              addDecl (Decl p x te)
          Typecheck -> do
              f <- getLastFile
              td <- typecheckDecl sd
              addDecl td
              opt <- getOpt
              td' <- if opt then optimizeDecl td else return td
              ppterm <- ppDecl td'
              printFD4 ppterm
          Eval -> do
              td <- typecheckDecl sd
              opt <- getOpt
              td' <- if opt then optimizeDecl td else return td
              ed <- evalDecl td'
              addDecl ed
          InteractiveCEK -> do
            td <- typecheckDecl sd
            opt <- getOpt
            td' <- if opt then optimizeDecl td else return td
            ed <- evalCEKDecl  td'
            addCEKDecl ed
            p <- getProf
            if p then do getOp >>= printFD4 . ("Cantidad de operaciones: "++) . show else return ()

          Bytecompile -> do
              td <- typecheckDecl sd             
              addDecl td

          CC -> do
              td <- typecheckDecl sd
              opt <- getOpt
              td' <- if opt then optimizeDecl td else return td
              addDecl td'
      where
        typecheckDecl :: MonadFD4 m => SDecl STerm -> m (Decl TTerm)
        typecheckDecl ssd =  do d <- elabDecl ssd
                                tcDecl  d
        optimizeDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
        optimizeDecl = optDeclaration

handleDecl st@SType {} = do
    let n = sinTypeName st
        v = sinTypeVal st
    res <- lookupSinTy n
    case res of
        Just _ -> failFD4 $ "La variable de tipo "++n++" ya fue definida"
        Nothing -> do v' <- desugarType v
                      addSinType n v'
                      return ()


data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines (reverse (nub (map declName glb))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compileFile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> handleDecl d
      Right t -> handleTerm t

handleTerm ::  MonadFD4 m => STerm -> m ()
handleTerm t = do
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         te <- eval tt
         ppte <- pp te
         printFD4 (ppte ++ " : " ++ ppTy (getTy tt))

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupDecl f
           _       -> return tex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "TTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t'<- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)

checkIsVal :: Ty -> Bool
checkIsVal NatTy  = True
checkIsVal _  = False

firstArgType :: Ty -> Ty
firstArgType (FunTy ty _) = ty
firstArgType ty = ty

