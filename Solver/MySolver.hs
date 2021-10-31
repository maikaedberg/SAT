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

find_uc ::  [(Int, [Lit])] -> Maybe Int
find_uc [] = Nothing
find_uc ((ind, lit):rest)
  | lit == [] = Just ind
  | otherwise = find_uc rest

replace :: (Int, [Lit]) -> [(Int, [Lit])] -> [(Int, [Lit])]
replace _ [] = []
replace (ind, lits) (x:xs) =
  if (ind == (fst x))
    then (ind, lits):xs
    else replace (ind, lits) xs

new_watches :: Int -> [Cls] -> [(Int, [Lit])] -> Maybe Lit
new_watches ind curr_clauses curr_watch = 
  case candidates of
    [] -> Nothing
    otherwise -> Just (head candidates)
  where
    cls = find_cls ind curr_clauses
    watched = 
      case lookup ind curr_watch of
        Nothing -> []
        Just s -> s
    candidates = [l | l <- literals cls, not (elem l watched)]

update_watchlist :: Lit -> [(Int, Maybe Lit)] -> [(Int, [Lit])] -> [(Int, [Lit])]
update_watchlist _ [] curr_watch = curr_watch
update_watchlist to_replace ((ind , newlit) : res) curr_watch =
  case newlit of
    Nothing -> replace (ind, []) curr_watch
    Just s -> replace (ind, [s, other_lit]) curr_watch
    where
      other_lit =
        case lookup ind curr_watch of
          Nothing -> Lit 0 False False -- will never happen
          Just lits -> head [l | l <- lits, l /= to_replace]

solve :: [Cls] -> [(Int, [Lit])] -> [Lit] -> Maybe Subst
solve [] _ _ = Just []
solve curr_clauses curr_watch all_lit =
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
      alt_watch = true_map all_lit (initialize_watched curr_watch)
      (cond, found_uc, uc_id) = 
        case find_uc curr_watch of
          Nothing -> (head (literals (head curr_clauses)), False, 0)
          Just sub -> (head (literals (find_cls sub curr_clauses)), True, sub)

      to_update_x = 
        case lookup (negLit cond) alt_watch of
          Nothing -> []
          Just lits -> lits
      updates_x = [ (n, new_watches n curr_clauses curr_watch ) | n <- to_update_x ]
      new_watch_x = [ c | c <- update_watchlist (negLit cond) updates_x curr_watch, fst c /= uc_id]

      to_update_negx = 
        case lookup (cond) alt_watch of
          Nothing -> []
          Just lits -> lits
      updates_negx = [ (n, new_watches n curr_clauses curr_watch ) | n <- to_update_negx ]
      new_watch_negx = update_watchlist cond updates_negx curr_watch

      cond_x    = condition cond curr_clauses
      cond_negx = condition (negLit cond) curr_clauses
      rho_x     = solve cond_x new_watch_x all_lit
      rho_negx  =
        case found_uc of
          True -> Nothing
          False -> 
            (solve cond_negx new_watch_negx all_lit)

solution :: CNF -> Maybe Subst
solution cnf =
  case solve curr_clauses curr_watch (all_literals cnf) of
    Nothing -> Nothing
    Just sub -> Just (fill (vars cnf) sub)
  where
    curr_clauses = clauses cnf
    curr_watch = init_watch_aux curr_clauses

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