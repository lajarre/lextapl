module Arith where

import Control.Applicative


data Term
  = TmTrue
  | TmFalse 
  | TmIf Term Term Term  
  | TmZero 
  | TmSucc Term 
  | TmPred Term 
  | TmIsZero Term
  deriving (Show, Eq)

isNumerical :: Term -> Bool
isNumerical TmZero = True
isNumerical (TmSucc t1) = isNumerical t1
isNumerical _ = False

isVal :: Term -> Bool
isVal TmTrue = True
isVal TmFalse = True
isVal t
  | isNumerical t = True
isVal _ = False


eval1 :: Term -> Maybe Term
eval1 (TmIf TmTrue t2 t3) = Just t2
eval1 (TmIf TmFalse t2 t3) = Just t3
eval1 (TmIf t1 t2 t3) = case eval1 t1 of
  Just t1' -> Just $ TmIf t1' t2 t3
  Nothing  -> Nothing
eval1 (TmSucc t1) = case eval1 t1 of
  Just t1' -> Just $ TmSucc t1'
  Nothing -> Nothing
eval1 (TmPred TmZero) = Just TmZero
eval1 (TmPred (TmSucc t1)) = Just t1
eval1 (TmPred t1) = case eval1 t1 of
  Just t1' -> Just $ TmPred t1'
  Nothing -> Nothing
eval1 (TmIsZero TmZero) = Just TmTrue
eval1 (TmIsZero (TmSucc t1))
  | isNumerical t1 = Just TmFalse
eval1 (TmIsZero t1) =  case eval1 t1 of
  Just t1' -> Just $ TmIsZero t1'
  Nothing -> Nothing
eval1 _ = Nothing

eval :: Term -> Term
eval t = maybe t eval (eval1 t)

evalBig :: Term -> Term
evalBig t
  | isVal t = t
evalBig (TmIf t1 t2 t3)
  | evalBig t1 == TmTrue && isVal (evalBig t2) = evalBig t2
  | evalBig t1 == TmFalse && isVal (evalBig t3) = evalBig t3
evalBig (TmSucc t1)
  | isNumerical (evalBig t1) = TmSucc $ evalBig t1
evalBig (TmPred t1) = case evalBig t1 of
  TmZero -> TmZero
  TmSucc t1' -> if isNumerical t1' then t1' else TmPred t1
  _ -> TmPred t1
evalBig (TmIsZero t1) = case evalBig t1 of
  TmZero -> TmTrue
  TmSucc t1' -> if isNumerical t1' then TmFalse else TmIsZero t1
  _ -> TmIsZero t1
evalBig t = t
