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
  if (elem ( BigOr [] ) (c:clauses))
    then Nothing -- If it contains an empty clause then it is trivially unsatisfiable,
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

find_unit_clause :: [Cls] -> [Cls] -> ([Cls], Bool)
-- looks for a unit clause 
-- returns unit clause at the head of the list if found
-- othewrise return what was given initally
find_unit_clause [] accum_cls = (accum_cls, False)
find_unit_clause (c:cls) accum_cls
  | (length (literals c)) == 1 = (c:(accum_cls ++ cls), True)
  | otherwise                  = find_unit_clause cls (c:accum_cls)
   
solve_up :: [Cls] -> Maybe Subst
solve_up [] = Just []
solve_up (c:clauses) =
  if (elem ( BigOr [] ) (c:clauses))
    then Nothing -- If it contains an empty clause then it is trivially unsatisfiable,
    else
      case rho_x of 
        Just l -> Just ((unLit cond):l)
        Nothing -> 
          case rho_negx of
            Just l -> Just ((unLit (negLit cond)):l)
            Nothing -> Nothing
    where
      (new_clauses, found_unit) = find_unit_clause (c:clauses) []
      cond = literals (head new_clauses) !! 0
      rest_clauses = tail new_clauses
      cond_x    = condition cond rest_clauses
      cond_negx = condition (negLit cond) rest_clauses
      rho_x     = (solve_up cond_x)
      rho_negx  = 
        case found_unit of
          True -> Nothing
          False -> (solve_up cond_negx)

neg_lit_in :: Lit -> [Cls] -> Bool
-- returns True if the negation of the literal is in clauses
--         False otherwise
neg_lit_in lit [] = False
neg_lit_in lit (c:clauses) = (elem (negLit lit) (literals c)) || (neg_lit_in lit clauses)

solve_u_le :: [Cls] -> Maybe Subst -- unit propogation ++ literal elimination
solve_u_le [] = Just []
solve_u_le (c:clauses) =
  if (elem ( BigOr [] ) (c:clauses))
    then Nothing -- If it contains an empty clause then it is trivially unsatisfiable,
    else
      case rho_x of 
        Just l -> Just ((unLit cond):l)
        Nothing -> 
          case rho_negx of
            Just l -> Just ((unLit (negLit cond)):l)
            Nothing -> Nothing
    where
      (new_clauses, found_unit) = find_unit_clause (c:clauses) []
      cond = literals (head new_clauses) !! 0
      rest_clauses = tail new_clauses
      cond_x    = condition cond rest_clauses
      cond_negx = condition (negLit cond) rest_clauses
      rho_x     = solve_u_le cond_x
      rho_negx  = 
        case found_unit of
          True -> Nothing
          False ->
            case neg_lit_in cond rest_clauses of
              True -> solve_u_le cond_negx
              False -> Nothing



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
  case solve_u_le (clauses cnf) of
    Nothing -> Nothing
    Just sub -> Just (fill (vars cnf) sub)


-- check for correctness + performance

solution_subsumption :: CNF -> Maybe Subst
solution_subsumption cnf = 
  case solve (clauses cnf') of
    Nothing -> Nothing
    Just sub -> do
            Just (fill (vars cnf') sub)
  where
    cnf' = subsumption cnf

