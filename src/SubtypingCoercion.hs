module SubtypingCoercion where

import           Control.Applicative
import           Data.List
import           Text.Printf
import           Data.Bifunctor
import           Data.Maybe

data Type = TyRecord [(String, Type)]
          | TyTop
          | TyArr Type Type
          | TyUnit
        deriving (Eq)

data Binding = NameBind
             | VarBind Type
             deriving (Show, Eq)

data Term = TmRecord [(String, Term)]
          | TmProj Term String
          | TmVar Int Int
          | TmAbs String Type Term
          | TmApp Term Term
          | TmUnit
        deriving (Eq)

type Context = [(String, Binding)]

data Typing = TypeError String 
            | Type (Type, Term)
            deriving (Eq, Show)

printTy :: Type -> String
printTy TyTop = "T"
printTy TyUnit = "U"
printTy (TyArr t1 t2) = printf "(%s → %s)" (printTy t1) (printTy t2)
printTy (TyRecord types) = printf $ "{" ++ foldl (\ acc (l, t) -> (if acc == "" then "" else acc ++ ", ") ++ l ++ ": " ++ printTy t) "" types ++ "}"

instance Show Type where
  show = printTy

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
printTm ctx TmUnit = printf "unit"

instance Show Term where
  show = printTm []


pickFreshName :: Context -> String -> (Context, String)
pickFreshName ctx x =
  case find ((== x) <$> fst) ctx of
    Just (x', b) -> pickFreshName ctx (x ++ "'")
    Nothing      -> ((x, NameBind):ctx, x)

addBinding :: Context -> String -> Binding -> Context
addBinding ctx x bind = (x, bind):ctx

getBinding :: Context -> Int -> Binding
getBinding ctx i = snd $ ctx !! i

getTypeFromContext :: Context -> Int -> Maybe Type
getTypeFromContext ctx i =
  case getBinding ctx i of
   VarBind ty -> Just ty
   _          -> Nothing

coerce :: Type -> Type
coerce TyTop = TyUnit
coerce (TyArr ty1 ty2) = TyArr (coerce ty1) (coerce ty2)
coerce (TyRecord fields) = TyRecord $ map (second coerce) fields
coerce TyUnit = TyUnit

-- Ideally should return only TmAbs terms. Maybe split Term in multiple
-- idependent types with shared classes?
subtype :: Context -> Type -> Type -> Either String (Context, Term)
subtype ctx tyS tyT |
  tyS == tyT =
    Right (ctx', TmAbs var tyS (TmVar 0 (length ctx')))
    where
      var = "x'coersametype"
      ctx' = addBinding ctx var (VarBind tyS)
subtype ctx tyS TyTop =
  Right (ctx', TmAbs var tyS TmUnit)
    where var = "x'coertop"
          ctx' = addBinding ctx var (VarBind tyS)
subtype ctx (TyArr s1't s2't) (TyArr t1't t2't) =
  case (subtype ctx t1't s1't, subtype ctx s2't t2't) of
    (Left errMsg1, _)                               -> Left $ "Arrow subtype image error: " ++ errMsg1
    (_, Left errMsg2)                               -> Left $ "Arrow subtype domain error: " ++ errMsg2
    (Right (ctx1, t1_s1's), Right (ctx2, s2_t2's))  ->
      Right
      (
        ctx'',
        TmAbs f s1_s2'c $
          TmAbs x t1'c $
            TmApp s2_t2's $
              TmApp (TmVar 1 (length ctx')) $
                TmApp t1_s1's (TmVar 0 (length ctx''))
      )
        where f = "f'coerapp"
              x = "x'coerapp"
              s1_s2'c = coerce (TyArr s1't s2't)
              t1'c = coerce t1't
              ctx' = addBinding ctx f (VarBind s1_s2'c)
              ctx'' = addBinding ctx' x (VarBind t1'c)
subtype ctx (TyRecord fs) (TyRecord ft) =
  case
    foldl
    (\ acc (li, fsi't) -> 
      case (acc, lookup li ft) of
        (Left errMsg, Nothing)  -> Left $ errMsg ++ " Missing field: " ++ li ++ "."
        (_, Nothing)            -> Left $ "Missing field: " ++ li ++ "."
        (acc, Just fti't) ->
          case (acc, subtype ctx fsi't fti't) of
            (Left errMsg, Left errMsgi) -> Left $ errMsg ++ " Subtype coercion error, field: " ++ li ++ "."
            (_, Left errMsgi)           -> Left $ "Subtype coercion error, field: " ++ li ++ "."
            (Left errMsg, _)            -> Left errMsg
            (Right accTerms, Right (_, coerTerm)) ->
              Right $ accTerms ++ [(li, TmApp coerTerm (TmProj (TmVar 0 1) li))]
    )
    (Right [])
    fs
  of
    Left errMsg       -> Left $ "RECORD SUBTYPING ERROR: " ++ errMsg
    Right coerTerms'  -> Right (ctx, TmAbs "r'coerrec" (TyRecord fs) (TmRecord coerTerms'))
subtype _ _ _ = Left "Subtyping error"


termShift :: Int -> Term -> Term
termShift d = walk 0 where
  walk :: Int -> Term -> Term
  walk c (TmVar i n) = if i >= c then TmVar (i + d) (n + d) else TmVar i (n + d)
  walk c (TmAbs x tyT1 t2) = TmAbs x tyT1 (walk (c + 1) t2)
  walk c (TmApp t1 t2) = TmApp (walk c t1) (walk c t2)
  walk c (TmRecord entries) = TmRecord $ map (second (walk c)) entries
  walk c a = a

typeOf :: Context -> Term -> Typing
typeOf ctx (TmVar i offset) = 
  case getTypeFromContext ctx i of
    Just ty -> Type (ty, TmVar i offset)
    _       -> TypeError $ "variable " ++ show i ++ "not a binding (should not a variable binding)"
typeOf ctx (TmAbs x tyT1 t2) =
  case typeOf ctx' t2 of
    Type (tyT2, t2'd) -> Type (TyArr tyT1 tyT2, TmAbs x (coerce tyT2) t2'd)
    TypeError errMsg  -> TypeError $ "lambda " ++ x ++" term type error, see:\n\t" ++ errMsg
  where ctx' = addBinding ctx x (VarBind tyT1)
typeOf ctx (TmApp t1 t2) =
  case (typeOf ctx t1, typeOf ctx t2)  of
    (TypeError errMsg1, _)                              -> TypeError $ "Applicator type error:\n\t" ++ errMsg1
    (_, TypeError errMsg2)                              -> TypeError $ "Argument type error:\n\t" ++ errMsg2
    (Type (TyArr t11't t12't, t1'd), Type (t2't, t2'd)) ->
      case subtype ctx t2't t11't of
        Left errMsg             -> TypeError $ "Parameter type mismatch:\n\t" ++ errMsg 
        Right (ctx', t2_t11's)  -> Type (t12't, TmApp t1'd (TmApp t2_t11's t2'd))
    _                                                   -> TypeError "Applicator not arrow type"
typeOf ctx (TmRecord fields) =
  either
  TypeError
  (\ (x, y) -> Type (TyRecord x, TmRecord y))
  (
    foldl
    (\ acc (li, fi) -> 
      case (acc, typeOf ctx fi) of
        (Left err, TypeError erri)  -> Left $ err ++ ", on label " ++ li ++ ": " ++ erri
        (Left err, _)               -> Left err
        (_, TypeError erri)         -> Left $ "Record typing error on label " ++ li ++ ": " ++ erri
        (Right (accFieldTypes, accFieldCoercions), Type (fi't, fi'c))
                                    -> Right (accFieldTypes ++ [(li, fi't)], accFieldCoercions ++ [(li, fi'c)])
    )
    (Right ([], []))
    fields
  )
typeOf ctx (TmProj t l) =
  case typeOf ctx t of
    Type (TyRecord t't, TmRecord t'c) ->
      case (lookup l t't, lookup l t'c) of
        (Just ti't, Just ti'c) -> Type (ti't, ti'c)
        (Just ti't, _)         -> TypeError "Projection on record with type/coercion mismatch" -- should not happen
        (_, Just ti'c)         -> TypeError "Projection on record with type/coercion mismatch" -- should not happen
        _                      -> TypeError $ "Projection on non-existing label " ++ show l
    Type _            -> TypeError "Projection on non-record"
    TypeError errMsg  -> TypeError errMsg

typeOf ctx TmUnit = Type (TyUnit, TmUnit)
