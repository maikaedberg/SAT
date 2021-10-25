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

-- https://baldur.iti.kit.edu/sat/files/2019/l08.pdf
count_occurence :: Lit -> [Cls] -> Int
count_occurence lit [] = 0
count_occurence lit (c:clauses) = 
  if (elem lit (literals c))
    then count_occurence lit clauses + 1
    else count_occurence lit clauses

greedy :: [Cls] -> Lit
greedy clauses = lit
  where
    no_occur = [(count_occurence l clauses, l) | l <- clauseLits clauses] -- [(int, lit)]
    max_occur = maximum [fst occur | occur <- no_occur] -- int
    lit = 
      case (lookup max_occur no_occur) of
        Just lit -> lit
        Nothing -> Lit 0 False -- will never happen

find_uc :: [Cls] -> [Cls] -> ([Cls], Bool)
-- looks for a unit clause 
-- returns unit clause at the head of the list if found
-- othewrise return what was given initally
find_uc [] accum_cls = (accum_cls, False)
find_uc (c:cls) accum_cls
  | (length (literals c)) == 1 = (c:(accum_cls ++ cls), True)
  | otherwise                  = find_uc cls (c:accum_cls)

neg_lit_in :: Lit -> [Cls] -> Bool
-- returns True if the negation of the literal is in one of the clauses
--         False otherwise
neg_lit_in lit [] = False
neg_lit_in lit (c:clauses) = (elem (negLit lit) (literals c)) || (neg_lit_in lit clauses)

solve :: [String] -> [Cls] -> Maybe Subst
solve _ [] = Just []
solve optimisations clauses =
  if (elem ( BigOr [] ) clauses)
    then Nothing -- If it contains an empty clause then it is trivially unsatisfiable
    else
      case rho_x of 
        Just l -> Just ((unLit cond):l)
        Nothing -> 
          case rho_negx of
            Just l -> Just ((unLit (negLit cond)):l)
            Nothing -> Nothing
    where
      (new_clauses, found_uc) = 
        case elem "-up" optimisations of
          True -> find_uc clauses []
          False -> (clauses, False)
      cond      = 
        case (elem "-greedy" optimisations) && (not found_uc) of
          True -> greedy new_clauses
          False -> head (literals (head new_clauses))
      found_neg_lit  = 
        case elem "-ple" optimisations of
          True -> neg_lit_in cond new_clauses
          False -> True
      cond_x    = condition cond new_clauses
      cond_negx = condition (negLit cond) new_clauses
      rho_x     = (solve optimisations cond_x)
      rho_negx  = 
        case found_uc of
          True -> Nothing
          False -> 
            case found_neg_lit of
              True -> (solve optimisations cond_negx)
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
  | elem True [subList y (literals c) | y <- (map literals cs)] = preprocess cs
  | otherwise                         = c:(preprocess cs)

subsumption :: CNF -> CNF
subsumption cnf = BigAnd (vars cnf) (preprocess (clauses cnf))

solution :: [String] -> CNF -> Maybe Subst
solution optimisations cnf = 
  case solve optimisations (clauses cnf') of
    Nothing -> Nothing
    Just sub -> Just (fill (vars cnf') sub)
  where
    cnf' = 
      case elem "-ss" optimisations of
        True -> subsumption cnf
        False -> cnf

