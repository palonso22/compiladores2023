module C ( ir2C ) where
import Prettyprinter
import Prettyprinter.Render.Terminal ( renderStrict )
import IR
import Lang
import Data.Text (unpack)
import Data.Char ( isAlpha, ord )

ty2doc :: IrTy -> Doc a
ty2doc IrInt = pretty "uint64_t"
ty2doc IrClo = pretty "clo"
ty2doc IrFunTy = pretty "fd4fun"

-- a -> ({a;})
-- Esto es una extensión de GNU C
exprstmt :: Doc a -> Doc a
exprstmt t = parens (braces (t <> semi))

{-decl2doc :: IrDecl -> Doc a
decl2doc (IrVal n ty t) = ty2doc ty <+> name n <> semi
decl2doc (IrFun n retTy args t) =
  let hdr = ty2doc retTy <+> name n <+> tupled (map (\(x, ty) -> ty2doc ty <+> name x) args) in
  let body = exprstmt (ir2doc t) in
  hdr <+>
  braces (nest 2 (line <> pretty "return" <+> body <> semi) <> line) <> line-}

decl2doc :: IrDecl -> Doc a
decl2doc (IrVal n t) = pretty "uint64_t" <+> name n <> semi
decl2doc (IrFun n tyr args t) =
 retTyToDoc tyr <+> name n <+> tupled (map (\(x,t) -> argTytoDoc x t) args) <+>
  braces (nest 2 (line <> pretty "return" <+> (ir2doc t) <> semi) <> line)


{-fd4Main :: [IrDecl] -> Doc a
fd4Main xs = pretty "uint64_t* fd4main()"
         <+> braces (nest 2 (line <> vsep (vals2doc xs ++ [pretty "return 0;"])) <> line)
  where vals2doc :: [IrDecl] -> [Doc a]
        vals2doc []               = []
        vals2doc (IrVal n ty t : ds) = (name n <+> pretty "=" <+> parens (ir2doc t) <> semi) : vals2doc ds
        vals2doc (_ : ds)         = vals2doc ds-}

argTytoDoc ::  Name -> Ty -> Doc a
argTytoDoc n ClosureTy =  let pr = pretty "void** " in
                           if n == "" then pr else  pr <+> name n

argTytoDoc n NatTy = let pr = pretty "uint64_t " in
                      if n == "" then pr else  pr <+> name n

argTytoDoc n (FunTy x t) =  let prettyName = if n == "" then pretty "" else name n in
                            retTyToDoc t <+> pretty " (*" <+> prettyName <> pretty ") (void**, " <+> (argTytoDoc "" x) <+> pretty ")"

argTytoDoc _ t = error $ "Error: tengo" ++ show t


fd4Main :: [IrDecl] -> Doc a
fd4Main xs = pretty "uint64_t* fd4main()"
         <+> braces (nest 2 (line <> vsep (vals2doc xs ++ [pretty "return 0;"])) <> line)
  where vals2doc :: [IrDecl] -> [Doc a]
        vals2doc []               = []
        vals2doc [IrVal n t]      = [name n <+> pretty "=" <+> voidptr <> parens (ir2doc t) <> semi, irPrintN (name n), semi]
        vals2doc (IrVal n t : ds) = (name n <+> pretty "=" <+> voidptr <> parens (ir2doc t) <> semi) : vals2doc ds
        vals2doc (_ : ds)         = vals2doc ds


name :: String -> Doc a
name n = pretty $ "fd4_" ++ escape n    --prefijo fd4 para evitar colision con nombres de C.

-- Convierte nombres con caracteres no válidos en C (como la comilla simple)
-- a nombres válidos.
escape = concatMap e1 where
  e1 :: Char -> String
  e1 c | c == '_'  = "__"
       | isAlpha c = [c]
       | otherwise = "_" ++ show (ord c)

stmt :: Doc a -> Doc a
stmt x = parens (braces (nest 2 (line <> x <> semi) <> line))

stmts:: [Doc a] -> Doc a
stmts xs = parens $ braces $
     foldr (\x ds -> nest 2 (line <> x <> semi) <> ds) line xs

voidptr :: Doc a
voidptr = parens (pretty "void *")

funcast :: Doc a
funcast = parens (pretty "fd4fun")

cast :: IrTy -> Doc a -> Doc a
cast ty d = parens (ty2doc ty) <> parens d

{-ir2doc :: Ir -> Doc a
ir2doc (IrVar n) = name n
ir2doc (IrGlobal n) = name n
ir2doc (IrCall f args ty) = cast ty (parens (funcast <+> ir2doc f) <> -- func
                                      tupled (map (\a -> voidptr <> ir2doc a) args)) -- args
ir2doc (IrConst (CNat n)) = pretty n
ir2doc (IrBinaryOp Add a b) = ir2doc a <+> pretty "+" <+> ir2doc b
ir2doc (IrBinaryOp Sub a b) = stmts [pretty "fd4_sub" <> tupled [ir2doc a, ir2doc b]]
ir2doc (IrLet n nty t t') = stmts [hsep [ty2doc nty, name n, pretty "=",  ir2doc t] <> semi <> line <> ir2doc t']
ir2doc (IrIfZ c a b) = parens $ sep [ir2doc c, nest 2 (pretty "?" <+> ir2doc b), nest 2 (colon <+> ir2doc a)]
ir2doc (IrPrint str t) = stmts [pretty "wprintf" <> parens (pretty "L" <> pretty (show str)),irPrintN (ir2doc t)]
ir2doc (MkClosure f args) = pretty "fd4_mkclosure" <> tupled (name f : pretty (length args) : map ir2doc args)
ir2doc (IrAccess t ty i) = cast ty $ parens (ir2doc t) <> brackets (pretty i) -}


ir2doc :: Ir -> Doc a
ir2doc (IrVar ty n) = name n
ir2doc (IrGlobal ty n) = name n
ir2doc (IrCall _ f args) =  ir2doc f <> tupled (map ir2doc args)
ir2doc (IrConst (CNat n)) = pretty n
ir2doc (IrBinaryOp Add a b) = ir2doc a <+> pretty "+" <+> ir2doc b
ir2doc (IrBinaryOp Sub a b) = stmts [pretty "fd4_sub" <> tupled [ir2doc a, ir2doc b]]
ir2doc (IrLet ty n t _ t') = stmts [hsep [argTytoDoc n ty, pretty "=",  ir2doc t] <> semi <> line <> ir2doc t']
ir2doc (IrIfZ ty c a b) = sep [ir2doc c, nest 2 (pretty "?" <+> ir2doc b), nest 2 (colon <+>  ir2doc a)]
ir2doc (IrPrint str t) = stmts [pretty "wprintf" <> parens (pretty "L" <> pretty (show str)),irPrintN (ir2doc t)]
ir2doc (MkClosure _ f args) = pretty "fd4_mkclosure" <> tupled (name f : pretty (length args) : map ir2doc args)
ir2doc (IrAccess t i) =  ir2doc t <> brackets (pretty i)


retTyToDoc :: Ty -> Doc a
retTyToDoc NatTy = pretty "uint64_t"
retTyToDoc (FunTy _ _) = pretty "void**"
retTyToDoc ty = error $ show ty


op2doc :: BinaryOp -> Doc a
op2doc Add = pretty "+"
op2doc Sub = pretty "-"

prelude :: Doc a
prelude = pretty "#include <inttypes.h>"
       <> line
       <> pretty "#include <wchar.h>"
       <> line
       <> pretty "typedef void * (*fd4fun)(void*, void*);"
       <> line
       <> pretty "typedef void **clo;"
       <> line
       <> pretty "extern void *fd4_mkclosure(void*, int, ...);"
       <> line
       <> pretty "extern uint64_t fd4_printn(uint64_t);"
       <> line
       <> pretty "extern uint64_t fd4_sub(uint64_t, uint64_t);"
       <> line

irPrintN :: Doc a -> Doc a
irPrintN x = pretty "fd4_printn" <> parens (exprstmt x) -- otro parens porque es una llamada a func

-- Simplemente llamar a esta función con las irDecls.
ir2C :: IrDecls -> String
ir2C (IrDecls xs) = unpack . renderStrict . layoutSmart defaultLayoutOptions $ vsep (prelude : map decl2doc xs ++ [fd4Main xs])
