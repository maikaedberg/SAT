module Solver.MySolver (solution) where

import CNF
import CNF.Eval

import Data.List
import Data.Maybe


fill :: [Var] -> Subst -> Subst
fill []     subst = subst
fill (v:vars) subst = 
  if elem v (fst (unzip subst)) 
    then fill vars subst
    else fill vars ((v, True):subst)

filterLit :: Lit -> Cls -> Maybe Cls
filterLit l c
    | elem l (literals c)          = Nothing -- literal found in clause
    | elem (negLit l) (literals c) = Just (BigOr (filter (/= negLit l) (literals c)) (index c)) -- neg literal found in clause
    | otherwise                    = Just c

condition :: Lit -> [Cls] -> [Cls]
condition l [] = []
condition l (c:cs) =
    case filterLit l c of
        Nothing -> condition l cs
        Just filtered ->  filtered:(condition l cs)

find_uc :: [Int] -> [(Lit, [Int])] -> Maybe Int
find_uc [] _ = Nothing
find_uc (ind:rest) alt_watch = 
  case find_uc rest alt_watch of
    Just i -> Just i
    Nothing -> 
      if not (elem ind (concat [snd i | i <- alt_watch]))
        then Just ind
        else Nothing

find_new_watch :: Lit -> Int -> [Cls] -> [(Lit, [Int])] -> [Lit]
find_new_watch _ _ _ [] = []
find_new_watch rid_of ind curr_clauses ((lit, clss) : rest)
  | rid_of == lit = prev
  | elem ind clss = lit : prev
  | elem lit (literals assoc_cls) = lit : prev
  | otherwise     = prev
  where
    prev = find_new_watch rid_of ind curr_clauses rest
    assoc_cls = find_cls ind curr_clauses
    
replace :: (Lit, [Int]) -> [(Lit, [Int])] -> [(Lit, [Int])]
replace (lit, ind) [] = []
replace (lit, ind) ((lit', ind'): rest) =
  if lit == lit' 
    then (lit, ind) : rest
    else replace (lit, ind) rest

append :: Int -> [Lit] -> [(Lit, [Int])] ->[(Lit, [Int])]
append _ _ [] = []
append n lits ((lit, ind) : rest) = 
  if elem lit lits
    then (lit, n : ind) : prev
    else prev
    where
      prev = append n lits rest

update_altwatch :: Lit -> [Int] -> [Cls] -> [(Lit, [Int])] -> [(Lit, [Int])]
update_altwatch _ [] _ alt_watch = alt_watch
update_altwatch rid_of (n: rest) curr_clauses alt_watch = alt_watch''
  where
    alt_watch' = replace (rid_of, []) alt_watch
    alt_watch'' = append n (find_new_watch rid_of n curr_clauses alt_watch) alt_watch'

solve :: [Cls] -> [(Lit, [Int])] -> Maybe Subst
solve [] _ = Just []
solve curr_clauses alt_watch =
  if (elem [] (map literals curr_clauses))
    then Nothing -- If it contains an empty clause then it is trivially unsatisfiable
    else
      case rho_x of
        Just l -> Just ((unLit cond):l)
        Nothing ->
          case rho_negx of
            Just l -> Just ((unLit (negLit cond)):l)
            Nothing -> Nothing
    where

      (cond, found_uc) = 
        case find_uc (map index curr_clauses) alt_watch of
          Nothing -> (head (literals (head curr_clauses)), False)
          Just sub -> (head (literals (find_cls sub curr_clauses)), True)

      to_update_x = 
        case lookup (negLit cond) alt_watch of
          Nothing -> []
          Just replace_clss -> replace_clss
      new_watch_x = update_altwatch (negLit cond) to_update_x curr_clauses alt_watch

      to_update_negx = 
        case lookup (cond) alt_watch of
          Nothing -> []
          Just replace_clss -> replace_clss
      new_watch_negx = update_altwatch (cond) to_update_negx curr_clauses alt_watch

      cond_x    = condition cond curr_clauses
      cond_negx = condition (negLit cond) curr_clauses
      rho_x     = solve cond_x new_watch_x
      rho_negx  =
        case found_uc of
          True -> Nothing
          False -> 
            (solve cond_negx new_watch_negx)

solution :: CNF -> Maybe Subst
solution cnf =
  case solve curr_clauses alt_watch of
    Nothing -> Nothing
    Just sub -> Just (fill (vars cnf) sub)
  where
    curr_clauses = clauses cnf
    curr_watch = init_watch_aux curr_clauses
    alt_watch = true_map (all_literals cnf) (initialize_watched curr_watch)

find_cls :: Int -> [Cls] -> Cls
find_cls i cls
  | index (head cls) == i = head cls
  | otherwise             = find_cls i (tail cls)

init_watch_aux :: [Cls] -> [(Int, [Lit])]
init_watch_aux [] = []
init_watch_aux (c:cls) 
  | length (literals c) < 2 = (index c, []) : init_watch_aux cls
  | otherwise               = (index c, [literals c !! 0, literals c !! 1]) : init_watch_aux cls

initialize_watched :: [(Int, [Lit])] -> [(Lit, Int)]
initialize_watched [] = []
initialize_watched ((n, lits) : rest) =
  [(l, n) | l <- lits] ++ (initialize_watched rest)

find_clsids :: Lit -> [(Lit, Int)] -> [Int]
find_clsids l [] = []
find_clsids l ((lit, ind): rest) = 
  if l == lit 
    then ind : find_clsids l rest
    else find_clsids l rest

true_map :: [Lit] -> [(Lit, Int)] -> [(Lit, [Int])]
true_map lits info = [(l, find_clsids l info) | l <- lits]
