module Subtyping where

import           Control.Applicative
import           Data.List
import           Text.Printf
import           Data.Bifunctor
import           Data.Maybe

data Type = TyRecord [(String, Type)]
          | TyTop
          | TyArr Type Type
          | TyBot
          | TyBool
        deriving (Show, Eq)

data Binding = NameBind
             | VarBind Type
             deriving (Show, Eq)

data Term = TmRecord [(String, Term)]
          | TmProj Term String
          | TmVar Int Int
          | TmAbs String Type Term
          | TmApp Term Term
          | TmTrue
          | TmFalse
          | TmIf Term Term Term
        deriving (Eq, Show)

type Context = [(String, Binding)]

data Typing = TypeError String | Type Type deriving (Eq, Show)


addBinding :: Context -> String -> Binding -> Context
addBinding ctx x bind = (x, bind):ctx

getBinding :: Context -> Int -> Binding
getBinding ctx i = snd $ ctx !! i

getTypeFromContext :: Context -> Int -> Maybe Type
getTypeFromContext ctx i =
  case getBinding ctx i of
   VarBind ty -> Just ty
   _          -> Nothing

subtype :: Type -> Type -> Maybe String
subtype tyS tyT |
  tyS == tyT = Nothing
subtype _ TyTop = Nothing
subtype TyBot _ = Nothing
subtype (TyRecord fS) (TyRecord fT) =
  foldl
  (\ acc (li, tyTi) -> 
    case (acc, lookup li fS) of
      (Nothing, Nothing)    -> Just $ "Subtyping error: record doesn't contain label(s): " ++ li
      (Just err, Nothing)   -> Just $ err ++ ", " ++ li
      (Nothing, Just tySi)  -> subtype tySi tyTi
      (Just err, Just tySi) ->
        maybe
        (Just err)
        (\ subErr -> Just $ err ++ ". With errors in item subtyping.\n" ++ subErr)
        (subtype tySi tyTi)
  )
  Nothing
  fT
subtype (TyArr tyS1 tyS2) (TyArr tyT1 tyT2) =
  case (subtype tyS1 tyT1, subtype tyS2 tyT2) of
    (Nothing, Nothing) -> Nothing
    (Just err, Nothing) -> Just $ "Subtyping error: Arrow type domain error\n" ++ err
    (Nothing, Just err) -> Just $ "Subtyping error: Arrow type image error\n" ++ err
    (Just err1, Just err2) -> Just $ "Subtyping error: Arrow type error domain and image error\n -" ++ err1 ++ "\n -" ++ err2
subtype _ _ = Just "Subtyping error: types mismatch"

join :: Type -> Type -> Type
join TyBool TyBool = TyBool
join (TyArr tyS1 tyS2) (TyArr tyT1 tyT2) =
  case maybeTyM1 of
    Just tyM1  -> TyArr tyM1 tyJ2
    Nothing -> TyTop
  where
    maybeTyM1 = meet tyS1 tyT2
    tyJ2 = join tyS2 tyT2
join (TyRecord fS) (TyRecord fT) =
  -- O(n2). Easily made O(n) if implementing Record type with a hashmap.
  TyRecord $ foldl (\ acc (li, (fSi, maybeFTi)) -> maybe acc (\ fTi -> acc ++ [(li, join fSi fTi)]) maybeFTi) [] maybeCommonTypes
    where
      maybeCommonTypes = (\ (li, fSi) -> (li, (fSi, lookup li fT))) <$> fS
join _ _ = TyTop

meet :: Type -> Type -> Maybe Type
meet TyBool TyBool = Just TyBool
meet _ TyTop = Just TyTop
meet TyTop _ = Just TyTop
meet (TyArr tyS1 tyS2) (TyArr tyT1 tyT2) =
  case maybeTyJ2 of
    Just tyJ2 -> Just $ TyArr tyM1 tyJ2
    Nothing -> Nothing
  where
    tyM1 = join tyS1 tyT1 
    maybeTyJ2 = meet tyS2 tyT2
meet (TyRecord fS) (TyRecord fT) =
  case maybeFSWithMeets of
    Just fSWithMeets -> Just $ TyRecord $ fSWithMeets ++ fTNoMeets
    Nothing -> Nothing
    where
      maybeFSWithMeets =
        foldl
        (\ acc (li, fSi) ->
          case (acc, lookup li fT) of
            (Nothing, _) -> Nothing
            (Just acc, Nothing) -> Just $ acc ++ [(li, fSi)]
            (Just acc, Just fTi) ->
              case meet fSi fTi of
                Just meetTyi -> Just $ acc ++ [(li, meetTyi)]
                Nothing -> Nothing
        )
        (Just [])
        fS
      fTNoMeets =
        foldl
        (\ acc (li, fTi) ->
          case lookup li fS of
            Just fSi -> acc
            Nothing -> acc ++ [(li, fTi)]
        )
        []
        fT
meet _ _ = Nothing

typeOf :: Context -> Term -> Typing
typeOf ctx (TmRecord fields) =
  either
  TypeError 
  (Type . TyRecord)
  (
    foldl 
    (\ acc (li, fi) ->
      case (acc, typeOf ctx fi) of 
        (Left err, TypeError erri)      -> Left $ err ++ ", on label " ++ li ++ ": " ++ erri
        (_, TypeError erri)             -> Left $ "Record typing error on label " ++ li ++ ": " ++ erri
        (Right accFieldTypes, Type fti) -> Right $ accFieldTypes ++ [(li, fti)]
    )
    (Right [])
    fields
  )
typeOf ctx (TmProj t1 l) =
  case typeOf ctx t1 of
    Type (TyRecord fieldTypes)  ->
      case typeLookup of
        Just typ -> Type typ
        Nothing -> TypeError $ "projection on non-existing label " ++ show l
      where typeLookup = lookup l fieldTypes
    Type TyBot                  -> Type TyBot
    TypeError errMsg            -> TypeError errMsg
    _ -> TypeError "projection on non-record"
typeOf ctx (TmVar i _) = 
  case getTypeFromContext ctx i of
    Just ty -> Type ty
    _       -> TypeError $ "variable " ++ show i ++ "not a binding (should not a variable binding)"
typeOf ctx (TmAbs x tyT1 t2) =
  case typeOf ctx' t2 of
    Type tyT2         -> Type $ TyArr tyT1 tyT2
    TypeError errMsg  -> TypeError $ "lambda " ++ x ++" term type error, see:\n\t" ++ errMsg
  where ctx' = addBinding ctx x (VarBind tyT1)
typeOf ctx (TmApp t1 t2) =
  case (tOf t1, tOf t2) of
    (Type (TyArr tyT11 tyT12), Type tyT2) ->
      case tyT2 `subtype` tyT11 of
         Nothing -> Type tyT12
         Just subtypeErr -> TypeError $ "Parameter type mismatch\n" ++ subtypeErr
    (Type TyBot, _ )                      -> Type TyBot
    _                                     -> TypeError "arrow type expected"
  where tOf = typeOf ctx
typeOf ctx TmTrue = Type TyBool
typeOf ctx TmFalse = Type TyBool
typeOf ctx (TmIf t1 t2 t3) =
  case (typeOf ctx t1, typeOf ctx t2, typeOf ctx t3) of
    (Type TyBool, Type ty2, Type ty3)                   -> Type $ join ty2 ty3
    (Type TyBool, TypeError errMsg2, TypeError errMsg3) -> TypeError $ "If clauses typing error, then: " ++ errMsg2 ++ ", else: " ++ errMsg3
    (Type TyBool, TypeError errMsg2, _)                 -> TypeError $ "If/then clause typing error: " ++ errMsg2
    (Type TyBool, _, TypeError errMsg3)                 -> TypeError $ "If/else clause typing error: " ++ errMsg3
    (Type _, _, _)                                      -> TypeError "If condition not boolean"
    (TypeError errMsg, _, _)                            -> TypeError $ "If condition typing error: " ++ errMsg

