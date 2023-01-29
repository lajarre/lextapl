module LetExercise where

import           Control.Applicative
import           Data.List
import           Text.Printf

data Type = TyBool
        | TyArr Type Type
        deriving (Eq)

data Binding = NameBind
             | VarBind Type
             deriving (Show, Eq)

data Term = TmTrue
          | TmFalse
          | TmIf Term Term Term
          | TmVar Int Int
          | TmAbs String Type Term
          | TmApp Term Term
          | TmLet String Term Term
          deriving (Eq)

type Context = [(String, Binding)]

printTy :: Type -> String
printTy TyBool        = "Bool"
printTy (TyArr t1 t2) = printf "(%s → %s)" (printTy t1) (printTy t2)

instance Show Type where
  show = printTy

pickFreshName :: Context -> String -> (Context, String)
pickFreshName ctx x =
  case find ((== x) <$> fst) ctx of
    Just (x', b) -> pickFreshName ctx (x ++ "'")
    Nothing      -> ((x, NameBind):ctx, x)

printTm :: Context -> Term -> String
printTm ctx (TmAbs x tyX t1) =
  let (ctx', x') = pickFreshName ctx x in
  printf "(lambda %s: %s. %s)" x' (show tyX) (printTm ctx' t1)
printTm ctx (TmApp t1 t2) =
  printf "(%s %s)" (printTm ctx t1) (printTm ctx t2)
printTm ctx (TmVar i n) =
  if length ctx == n
     then printf "%s" (fst (ctx !! i))
     else printf "[bad index]"
printTm ctx TmTrue = printf "true"
printTm ctx TmFalse = printf "false"
printTm ctx (TmLet x t1 t2) =
  printf "(let %s=%s in %s)" x (printTm ctx t1) (printTm ctx t2)

instance Show Term where
  show = printTm []


addBinding :: Context -> String -> Binding -> Context
addBinding ctx x bind = (x, bind):ctx

getBinding :: Context -> Int -> Binding
getBinding ctx i = snd $ ctx !! i

getTypeFromContext :: Context -> Int -> Maybe Type
getTypeFromContext ctx i =
  case getBinding ctx i of
   VarBind ty -> Just ty
   _          -> Nothing

data Typing = TypeError String | Type Type deriving (Eq)

printTypingResult :: Typing -> String
printTypingResult (TypeError errMsg) = printf $ "Typing error: " ++ errMsg ++ "\n"
printTypingResult (Type ty)          = printf $ "Type: " ++ show ty ++ "\n"

instance Show Typing where
  show = printTypingResult

typeOf :: Context -> Term -> Typing
typeOf ctx TmTrue = Type TyBool
typeOf ctx TmFalse = Type TyBool
-- 👓 https://wiki.haskell.org/Let_vs._Where
typeOf ctx (TmIf t1 t2 t3)
  | tOf t1 == Type TyBool && tOf t2 == tOf t3 = tOf t2
  | tOf t1 == Type TyBool = TypeError "arms of conditional have different types"
  | otherwise = TypeError "guard of conditional not a boolean"
  where tOf = typeOf ctx
typeOf ctx (TmVar i _) =
  case getTypeFromContext ctx i of
    Just ty -> Type ty
    _ -> TypeError $ "variable " ++ show i ++ "not a binding (should not a variable binding)"
typeOf ctx (TmAbs x tyT1 t2) =
  case typeOf ctx' t2 of
    Type tyT2 ->  Type $ TyArr tyT1 tyT2
    TypeError errMsg -> TypeError $ "lambda " ++ x ++" term type error, see:\n\t" ++ errMsg
  where ctx' = addBinding ctx x (VarBind tyT1)
typeOf ctx (TmApp t1 t2) =
  case tOf t1 of
    Type (TyArr tyT11 tyT12) ->
      if tOf t2 == Type tyT11
         then Type tyT12
         else TypeError "parameter type mismatch"
    _ -> TypeError "arrow type expected"
  where tOf = typeOf ctx
typeOf ctx (TmLet x t1 t2) =
  case typeOf ctx t1 of
    Type tyT1 ->
      case typeOf ctx' t2 of
        Type tyT2 -> Type tyT2
        TypeError errMsg -> TypeError $ "let " ++ x ++ " body term type error, see:\n\t" ++ errMsg
      where ctx' = addBinding ctx x (VarBind tyT1)
    TypeError errMsg -> TypeError $ "let " ++ x ++ " bound term type error, see:\n\t" ++ errMsg

termShift :: Int -> Term -> Term
termShift d = walk 0 where
  walk :: Int -> Term -> Term
  walk c (TmVar i n) = if i >= c then TmVar (i + d) (n + d) else TmVar i (n + d)
  walk c (TmAbs x tyT1 t2) = TmAbs x tyT1 (walk (c + 1) t2)
  walk c (TmApp t1 t2) = TmApp (walk c t1) (walk c t2)
  walk c (TmLet x t1 t2) = TmLet x t1 (walk (c + 1) t2)
  walk c a = a

termSubst :: Int -> Term -> Term -> Term
termSubst j s = walk 0 where
  walk :: Int -> Term -> Term
  -- c counts the abstraction depth:
  walk c (TmVar i n)       = if j + c == i then termShift c s else TmVar i n
  walk c (TmAbs x tyT1 t2) = TmAbs x tyT1 (walk (c + 1) t2)
  walk c (TmApp t1 t2)     = TmApp (walk c t1) (walk c t2)
  walk c (TmLet x t1 t2)   = TmLet x t1 (walk (c + 1) t2)
  walk c a                 = a

termSubsTop :: Term -> Term -> Term
termSubsTop v t = termShift (-1) $ termSubst 0 (termShift 1 v) t

isVal :: Context -> Term -> Bool
isVal ctx TmTrue     = True
isVal ctx TmFalse    = True
isVal ctx (TmAbs {}) = True
isVal _ _            = False

eval1 :: Context -> Term -> Maybe Term
eval1 _ (TmIf TmTrue t2 t3) = Just t2
eval1 _ (TmIf TmFalse t2 t3) = Just t3
eval1 ctx (TmIf t1 t2 t3) = case eval1 ctx t1 of
  Just t1' -> Just $ TmIf t1' t2 t3
  Nothing  -> Nothing
eval1 ctx (TmApp (TmAbs x tyT1 t12) v2) | isVal ctx v2 =
  Just $ termSubsTop v2 t12
eval1 ctx (TmApp v1 t2) | isVal ctx v1 =
  case eval1 ctx t2 of
    Just t2' -> Just $ TmApp v1 t2'
    Nothing  -> Nothing
-- eval1 ctx (TmApp t1 t2) = (Just <$> (`TmApp` t2)) =<< eval1 ctx t1
eval1 ctx (TmApp t1 t2) =
  case eval1 ctx t1 of
    Just t1' -> Just $ TmApp t1' t2
    Nothing  -> Nothing
eval1 ctx (TmLet x v1 t2) | isVal ctx v1 =
  Just $ termSubsTop v1 t2
eval1 ctx (TmLet x t1 t2) =
  case eval1 ctx t1 of
    Just t1' -> Just $ TmLet x t1' t2
    Nothing  -> Nothing
eval1 _ _ = Nothing

eval :: Context -> Term -> Term
eval ctx t = maybe t (eval ctx) (eval1 ctx t)



expr = TmApp
  expr1
  expr2

expr1 = TmAbs "x" (TyArr TyBool TyBool) (TmVar 0 1)

expr2 = TmApp
    expr21
    expr22

expr21 = TmAbs "z" (TyArr TyBool TyBool) (TmApp
    (TmAbs "x" (TyArr TyBool TyBool) (TmVar 0 2))
    (TmVar 0 1)
  )

expr22 = TmAbs "x" TyBool (TmVar 0 1)
