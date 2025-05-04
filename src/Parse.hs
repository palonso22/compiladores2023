{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)
import qualified Data.Foldable

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P Ty
tyatom = do reserved "Nat" >> return NatTy
         <|> (varST >>= \n->return $ SinTy n)
         <|> parens typeP

typeP :: P Ty
typeP = try (do x <- tyatom
                reservedOp "->"
                FunTy x <$> typeP)
        <|> tyatom
          
const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral  
  return (SLam i [("xx_print", NatTy)] (SPrint i str (SV i "xx_print")))
  
  

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea una lista de (variable : tipo)
binding :: P [(Name, Ty)]
binding = do v <- many var
             reservedOp ":"
             ty <- typeP
             return [(n,ty)| n <- v]

-- parsea un par (variable : tipo)
oneBinding :: P (Name, Ty)
oneBinding = do v <- var
                reservedOp ":"
                ty <- typeP
                return (v,ty)


binder ::P [(Name, Ty)]
binder = parens binding

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         vars <- many binder         
         reservedOp "->"
         t <- expr
         let vars' = Data.Foldable.concat vars
         return (SLam i vars' t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens oneBinding
         vars <- many binder         
         let vars' = Data.Foldable.concat vars
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) vars' t)

letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  isRec <- parseRec
  name <- var
  vars <- many binder 
  let vars' = Data.Foldable.concat vars
  reservedOp ":"
  retty <- typeP
  reservedOp "="
  def <- expr
  reserved "in"
  SLet i isRec name vars' retty def <$> expr

parseRec :: P Bool
parseRec = (reserved "rec" >> return True) <|> return False


-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

-- | Parser de declaraciones
decl :: P (SDecl STerm)
decl = do
     i <- getPos
     reserved "let"
     b <- parseRec
     name <- var
     ls <- many binder
     let ls' = Data.Foldable.concat ls 
     reservedOp ":"
     ty <-  typeP
     reservedOp "="
     e <- expr
     return $ SDecl i b name ls' ty e

-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl STerm]
program = many $ declOrSintype

declOrSintype :: ParsecT String () Identity (SDecl STerm)
declOrSintype = try (decl <|> sintype)

sintype::P (SDecl a)
sintype = do reserved "type"
             name <- var
             reservedOp "="
             value <- typeP
             return $ SType name value



-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm =  try (Left <$> decl) <|> (Right <$> expr)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)

-- Esto se usa para sinonimos de tipo
varST :: P Name
varST = identifierST

identifierST :: P String
identifierST = Tok.identifier lexerST

-- creamos un nuevo lexer que no tenga como palabras reservadas Nat y ->
lexerST ::Tok.TokenParser u
lexerST = Tok.makeTokenParser $
          emptyDef {
          commentLine    = "#",
          reservedNames = ["let", "fun", "fix", "then", "else","in",
                           "ifz", "print"],
          reservedOpNames = [":","=","+","-"]
          }



