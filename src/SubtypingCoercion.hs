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
        deriving (Show, Eq)

data Binding = NameBind
             | VarBind Type
             deriving (Show, Eq)

data Term = TmRecord [(String, Term)]
          | TmProj Term String
          | TmVar Int Int
          | TmAbs String Type Term
          | TmApp Term Term
          | TmUnit
        deriving (Eq, Show)

type Context = [(String, Binding)]
type ContextPrefix = [(String, Binding)]

data Typing = TypeError String 
            | Type (Type, Term)
            deriving (Eq, Show)

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
    Right (ctx', TmAbs var tyS (TmVar 0 1))
    where
      var = "x'coersametype"
      ctx' = addBinding ctx var (VarBind tyS)
subtype ctx tyS TyTop =
  Right (ctx', TmAbs var tyS TmUnit)
    where var = "x'coertop"
          ctx' = addBinding ctx var (VarBind tyS)
subtype ctx (TyArr s1't s2't) (TyArr t1't t2't) =
  case (subtype ctx t1't s1't, subtype ctx s2't t2't) of
    (Left errMsg1, _)                               -> Left $ "Arrow applicator subtype error:\n\t" ++ errMsg1
    (_, Left errMsg2)                               -> Left $ "Arrow argument subtype error:\n\t" ++ errMsg2
    (Right (ctx1, t1_s1's), Right (ctx2, s2_t2's))  -> Right
      (
        ctx'',
        TmAbs f s1_s2'c $
          TmAbs x t1'c $
            TmApp s2_t2's $
              TmApp (TmVar 1 2) $
                TmApp t1_s1's (TmVar 0 2)
      )
        where f = "f'coerapp"
              x = "x'coerapp"
              s1_s2'c = coerce (TyArr s1't s2't)
              t1'c = coerce t1't
              ctx' = addBinding ctx f (VarBind s1_s2'c)
              ctx'' = addBinding ctx' x (VarBind t1'c)
-- subtype ctx (TyRecord fS) (TyRecord fT) =
--   SubtypeCoercion r [(kj, snd (typeOf fSj))] [(li, (subtype fSi fTi) (lookup li r)]
--   where (ctx', r) = pickFreshName ctx "subtypecoerRecord"
-- 
--   foldl
--   (\ acc (li, tyTi) -> 
--     case (acc, lookup li fS) of
--       (Nothing, Nothing)    -> Left $ "Subtyping error: record doesn't contain label(s): " ++ li
--       (Just err, Nothing)   -> Left $ err ++ ", " ++ li
--       (Nothing, Just tySi)  -> subtype tySi tyTi
--       (Just err, Just tySi) ->
--         maybe
--         (Just err)
--         (\ subErr -> Just $ err ++ ". With errors in item subtyping.\n" ++ subErr)
--         (subtype tySi tyTi)
--   )
--   ????
--   fT
subtype _ _ _ = Left "Subtyping error" -- [XXX]
-- subtype _ TyBot _ = Nothing
-- subtype (TyRecord fS) (TyRecord fT) =
--   foldl
--   (\ acc (li, tyTi) -> 
--     case (acc, lookup li fS) of
--       (Nothing, Nothing)    -> Just $ "Subtyping error: record doesn't contain label(s): " ++ li
--       (Just err, Nothing)   -> Just $ err ++ ", " ++ li
--       (Nothing, Just tySi)  -> subtype tySi tyTi
--       (Just err, Just tySi) ->
--         maybe
--         (Just err)
--         (\ subErr -> Just $ err ++ ". With errors in item subtyping.\n" ++ subErr)
--         (subtype tySi tyTi)
--   )
--   Nothing
--   fT
-- subtype (TyArr tyS1 tyS2) (TyArr tyT1 tyT2) =
--   case (subtype tyS1 tyT1, subtype tyS2 tyT2) of
--     (Nothing, Nothing) -> Nothing
--     (Just err, Nothing) -> Just $ "Subtyping error: Arrow type domain error\n" ++ err
--     (Nothing, Just err) -> Just $ "Subtyping error: Arrow type image error\n" ++ err
--     (Just err1, Just err2) -> Just $ "Subtyping error: Arrow type error domain and image error\n -" ++ err1 ++ "\n -" ++ err2
-- subtype _ _ = Just "Subtyping error: types mismatch"


replaceAbsType :: Term -> Type -> Term
replaceAbsType (TmAbs x tyX t1) ty = TmAbs x ty t1
replaceAbsType term _ = term

typeOf :: Context -> Term -> Typing
-- typeOf ctx (TmRecord fields) =
--   either
--   TypeError 
--   (Type . TyRecord)
--   (
--     foldl 
--     (\ acc (li, fi) ->
--       case (acc, typeOf ctx fi) of 
--         (Left err, TypeError erri)      -> Left $ err ++ ", on label " ++ li ++ ": " ++ erri
--         (_, TypeError erri)             -> Left $ "Record typing error on label " ++ li ++ ": " ++ erri
--         (Right accFieldTypes, Type fti) -> Right $ accFieldTypes ++ [(li, fti)]
--     )
--     (Right [])
--     fields
--   )
-- typeOf ctx (TmProj t1 l) =
--   case typeOf ctx t1 of
--     Type (TyRecord fieldTypes)  ->
--       case typeLookup of
--         Just typ -> Type typ
--         Nothing -> TypeError $ "projection on non-existing label " ++ show l
--       where typeLookup = lookup l fieldTypes
--     TypeError errMsg            -> TypeError errMsg
--     _                           -> TypeError "projection on non-record"
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
-- typeOf ctx (TmApp (TmAbs t1x t1XType t1Term) t2) =
--   case typeOf ctx t2 of
--     TypeError errMsg    -> TypeError $ "Right term type error in App:\n\t" ++ errMsg
--     Type (tyT2, coerT2) ->
--       case subtype ctx tyT2 t1XType of
--         Left subtypeErr ->
--           TypeError $ "Parameter type mismatch:\n\t" ++ subtypeErr
--         Right (ctx', SubtypeCoercion coerX coerXType coerTerm) ->
--           typeOf ctx' $ -- [xxx] sure?
--             TmApp
--             (TmAbs coerX coerXType coerTerm)
--             (TmApp (TmAbs t1x tyT2 t1Term) t2)
--             -- No. t1Term needs coercion as well.
typeOf ctx TmUnit = Type (TyUnit, TmUnit)
