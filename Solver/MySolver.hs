module Solver.MySolver (solution) where

import CNF
import CNF.Eval

import Data.List
import Data.Maybe

fill :: [Var] -> Subst -> Subst
fill []     subst = subst
fill (v:vars) subst = 
  if elem v [fst s | s <- subst]
    then fill vars subst
    else fill vars ((v, True):subst)
    
solve :: [Cls] -> Maybe Subst
solve [] = Just []
solve (c:clauses) =
  -- If it contains an empty clause then it is trivially unsatisfiable,
  if (elem ( BigOr [] ) (c:clauses))
    then Nothing
    else 
      case rho_x of 
        Just l -> Just ((unLit cond):l)
        Nothing -> 
          case rho_negx of
            Just l -> Just ((unLit (negLit cond)):l)
            Nothing -> Nothing
    where
      cond      = head (literals c)
      cond_x    = condition cond (c:clauses)
      cond_negx = condition (negLit cond) (c:clauses)
      rho_x     = (solve cond_x)
      rho_negx  = (solve cond_negx)

filterLit :: Lit -> Cls -> Maybe Cls
filterLit l c
    | elem l (literals c)          = Nothing -- literal found in clause
    | elem (negLit l) (literals c) = Just (BigOr (filter (/= (negLit l)) (literals c))) -- neg literal found in clause
    | otherwise                    = Just c

condition :: Lit -> [Cls] -> [Cls]
condition l [] = []
condition l (c:cs) = 
    case (filterLit l c) of
        Nothing -> condition l cs
        Just filtered ->  filtered:(condition l cs)

--https://stackoverflow.com/questions/47232335/check-if-list-is-a-sublist-of-another-list
subList :: Eq a => [a] -> [a] -> Bool
subList [] [] = True
subList _ []    = False
subList [] _    = True
subList (x:xs) (y:ys) 
    | x == y    = subList xs ys   
    | otherwise = subList (x:xs) ys

preprocess :: [Cls] -> [Cls]
preprocess [] = []
preprocess (c:cs)
  | elem True [subList (literals c) y | y <- (map literals cs)] = preprocess cs
  | otherwise                         = c:(preprocess cs)

subsumption :: CNF -> CNF
subsumption cnf = BigAnd (vars cnf) (preprocess (clauses cnf))

solution :: CNF -> Maybe Subst
solution cnf = 
  case solve (clauses cnf') of
    Nothing -> Nothing
    Just sub -> do
            Just (fill (vars cnf') sub)
  where
    cnf' = subsumption cnf

