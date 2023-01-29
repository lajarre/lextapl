module Lambda where

import qualified Arith               as A
import           Control.Applicative
import           Data.List
import           Text.Printf

data Term = TmVar Int Int
          | TmAbs String Term
          | TmApp Term Term
          deriving (Eq)

data Binding = NameBind deriving (Show, Eq, Ord)

type Context = [(String, Binding)]

pickFreshName :: Context -> String -> (Context, String)
pickFreshName ctx x =
  case find ((== x) <$> fst) ctx of
    Just (x', b) -> pickFreshName ctx (x ++ "'")
    Nothing      -> ((x, NameBind):ctx, x)

printTm :: Context -> Term -> String
printTm ctx (TmAbs x t1) =
  let (ctx', x') = pickFreshName ctx x in
  printf "(lambda %s. %s)" x' (printTm ctx' t1)
printTm ctx (TmApp t1 t2) =
  printf "(%s %s)" (printTm ctx t1) (printTm ctx t2)
printTm ctx (TmVar i n) =
  if length ctx == n
     then printf "%s" (fst (ctx !! i))
     else printf "[bad index]"

instance Show Term where
  show = printTm []

termShift :: Int -> Term -> Term
termShift d = walk 0 where
  walk :: Int -> Term -> Term
  walk c (TmVar i n) = if i >= c then TmVar (i + d) (n + d) else TmVar i (n + d)
  walk c (TmAbs x t1) = TmAbs x (walk (c + 1) t1)
  walk c (TmApp t1 t2) = TmApp (walk c t1) (walk c t2)

termSubst :: Int -> Term -> Term -> Term
termSubst j s = walk 0 where
  walk :: Int -> Term -> Term
  -- c counts the abstraction depth:
  walk c (TmVar i n)   = if j + c == i then termShift c s else TmVar i n
  walk c (TmAbs x t1)  = TmAbs x (walk (c + 1) t1)
  walk c (TmApp t1 t2) = TmApp (walk c t1) (walk c t2)

termSubsTop :: Term -> Term -> Term
termSubsTop v t = termShift (-1) $ termSubst 0 (termShift 1 v) t

isVal :: Context -> Term -> Bool
isVal ctx (TmAbs _ _) = True
isVal _ _             = False

eval1 :: Context -> Term -> Maybe Term
eval1 ctx (TmApp (TmAbs x t12) v2) |
  isVal ctx v2 =
    Just $ termSubsTop v2 t12
eval1 ctx (TmApp v1 t2) |
  isVal ctx v1 =
    case eval1 ctx t2 of
      Just t2' -> Just $ TmApp v1 t2'
      Nothing  -> Nothing
-- eval1 ctx (TmApp t1 t2) = (Just <$> (`TmApp` t2)) =<< eval1 ctx t1
eval1 ctx (TmApp t1 t2) =
  case eval1 ctx t1 of
    Just t1' -> Just $ TmApp t1' t2
    Nothing  -> Nothing
eval1 _ _ = Nothing

eval :: Context -> Term -> Term
eval ctx t = maybe t (eval ctx) (eval1 ctx t)

evalBig :: Context -> Term -> Term
evalBig ctx t |
  isVal ctx t = t
evalBig ctx (TmApp (TmAbs x t12) t2) |
  isVal ctx (evalBig ctx t2) && isVal ctx (evalBig ctx (termSubsTop (evalBig ctx t2) t12)) =
    evalBig ctx (termSubsTop (evalBig ctx t2) t12)
evalBig ctx t = t

expr = TmApp
  (TmAbs "x" (TmVar 0 1))
  (TmApp
    (TmAbs "x" (TmVar 0 1))
    (TmAbs "z" (TmApp
      (TmAbs "x" (TmVar 0 2))
      (TmVar 0 1)
    ))
  )
