module Solver.MySolver (solution) where

import CNF
import CNF.Eval

import Data.List
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map












fill :: [Var] -> Subst -> Subst
fill []     subst = subst
fill (v:vars) subst = 
  if elem v (fst (unzip subst)) 
    then fill vars subst
    else fill vars ((v, True):subst)

initialize :: [Cls] -> [Cls]
initialize [] = []
initialize (c:[]) = [BigOr (literals c) 1]
initialize (c:cls) =  BigOr (literals c) (1 + prev_count) : prev_cls
  where
    prev_cls = initialize cls
    prev_count = index (head (initialize cls))

find_cls :: Int -> [Cls] -> Cls
find_cls i cls
  | index (head cls) == i = head cls
  | otherwise             = find_cls i (tail cls)

replace_lit :: Lit -> Lit -> Cls -> Maybe Lit
replace_lit lit lit_other clause
  | active_lits == [] = Nothing
  | otherwise    = 
    case active_lits of
      [] -> Nothing
      otherwise -> Just (head active_lits)
  where
    active_lits = [l | l <- literals clause, active l, l /= lit_other]

-- create map, get a nice map doing Map.fromList (initialize_watched clauses)
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

update :: Cls -> Lit -> Lit -> Maybe Lit
-- if update fails -> Unit propogation
update cls lit1 lit2 =
  case candidates of
    [] -> Nothing
    otherwise -> head candidates
    where 
      candidates = [l | l <- literals cls, l /= lit1, l /= lit2]

update_watch :: [Cls] -> [(Lit, [Int])] -> [(Lit, [Int])]
update_watch [] _ = []
update_watch (c:cls) info = 
  update c 




solve :: [Cls] -> [(Int, [Lit])] -> [(Lit, [Int])] -> Maybe Subst
solve curr_clauses curr_watch alt_watch =
  
  where
    cond = 
      case find_uc curr_watch of
        Nothing -> head (literals (head curr_clauses))
        Just sub -> head (literals (find_cls sub curr_clauses))
    -- all clauses that need to be updated with new watches
    to_update = 
      case lookup (negLit cond) alt_watch of
        Nothing -> []
        Just lits -> lits





deactivate :: Lit -> Lit
deactivate (Lit v b a) = Lit v b False

deactivate_lits :: Lit -> [Lit] -> [Lit]
deactivate_lits _ [] = []
deactivate_lits to_deac (l:lits)
  | l == (negLit to_deac) = (deactivate l) : (deactivate_lits to_deac lits)
  | otherwise             = l : (deactivate_lits to_deac lits)

find_uc ::  [(Int, [Lit])] -> Maybe Int
find_uc [] = Nothing
find_uc ((ind, lit):rest)
  | lit == [] = Just ind
  | otherwise = find_uc rest





-- update_watch :: Lit -> [Cls] -> [(Int, [Lit])] -> [(Int, [Lit])]
-- update_watch _ _ [] = []
-- update_watch lit clauses ((ind, l): rest)
--   | l == [] = (ind, l): (update_watch lit clauses rest)
--   | lit == l !! 0 =
--     case replace_lit lit (l !! 1) (find_cls ind clauses) of
--       Nothing -> (ind, []): (update_watch lit clauses rest)
--       Just replace ->  ( ind, ( [replace, l !! 1 ] ) ) : (update_watch lit clauses rest)
--   | lit == l !! 1 = 
--      case replace_lit lit (l !! 0) (find_cls ind clauses) of
--       Nothing -> (ind, []): (update_watch lit clauses rest)
--       Just replace ->  ( ind, ( [replace, l !! 0 ] ) ) : (update_watch lit clauses rest)
--   | otherwise = (ind, l): (update_watch lit clauses rest)




-- solve2 :: [(Int, [Lit])] -> [Cls] -> Maybe Subst
-- solve2 curr_watch [] = Nothing
-- solve2 curr_watch curr_clauses
--   | active_clauses == [] = Just []
--   | otherwise = do

--     let cond = head [l | l <- literals (head active_clauses), active l]

--     let cond_x =    [BigOr (deactivate_lits cond (literals c)) (index c) | c <- curr_clauses]
--     let sol_x = solve2 curr_watch cond_x
--     let cond_negx = [BigOr (deactivate_lits (negLit cond) (literals c)) (index c) | c <- curr_clauses]
--     let sol_negx =  solve2 curr_watch cond_negx
    
--     case sol_x of
--       Nothing -> 
--         case sol_negx of
--           Nothing -> Nothing
--           Just sub -> Just ((unLit (negLit cond)): sub)
--       Just sub -> Just (unLit cond : sub)

--   where
--     active_clauses = [c | c <- curr_clauses, isactive c]

-- solve :: [(Int, [Lit])] -> [Cls] -> Maybe Subst
-- solve curr_watch [] = Nothing
-- solve curr_watch curr_clauses =
--   case length active_clauses of
--     0 -> Just []
--     otherwise -> 
--       case cond of 
--         Nothing -> Nothing
--         Just sub -> 
--           case solve new_watch new_clauses of
--             Nothing -> Nothing
--             Just rest -> Just ((unLit sub): rest)
--             where 
--               new_clauses = [BigOr (deactivate_lits sub (literals c)) (index c) | c <- curr_clauses]
--               new_watch = update_watch sub new_clauses curr_watch
--   where
--     active_clauses = [c | c <- curr_clauses, isactive c]
--     cond = 
--       case find_uc curr_watch of
--         Nothing -> Just (head (literals (head active_clauses)))
--         Just ind  -> 
--           case candidates of
--             [] -> Nothing
--             otherwise -> Just (head candidates)
--             where
--               candidates = [l | l <- literals (find_cls ind active_clauses), active l]

-- now, map [Cls] -> [[Lit]]

-- intialize_watched :: [Cls] -> ([Cls], [Cls]) -- ([Unit clauses], [rest of cluases w/ updated watch list])
-- intialize_watched [] = ([] , [])
-- intialize_watched (c:cls) = (ucls ++ prev_ucls, (BigOr (literals c) w_lits : prev_watched) )
--   where
--     (prev_ucls, prev_watched) = intialize_watched cls
--     (ucls, w_lits) = 
--       case length (literals c) > 1 of
--         True -> ([], [(literals c) !! 0, (literals c) !! 1])
--         False -> ([c], [])

-- remove_watch :: Bool -> Cls -> Maybe Cls 
-- -- returns Nothing if it's a unit clause, returns Just cls w/ update watch
-- -- first argument True -> remove first, False -> remove second
-- remove_watch to_remove (BigOr lits w_lits)
--   | length lits == 1 = Nothing
--   | otherwise = Just (BigOr lits new_watch_list)
--   where
--     new_watch = head ([l | l <- lits, not (elem l w_lits), not (elem (negLit l) w_lits)])
--     new_watch_list
--       | to_remove = [new_watch, w_lits !! 1]
--       | otherwise = [w_lits !! 0, new_watch]

-- lit_watched :: Bool -> Lit -> Cls -> Bool
-- lit_watched True lit c = 
--   (lit == (watched c) !! 0) || ((negLit lit) == (watched c) !! 0)
-- lit_watched False lit c = 
--   (lit == (watched c) !! 1) || ((negLit lit) == (watched c) !! 1)

-- update_watched :: Lit -> [Cls] -> ([Cls], [Cls])
-- update_watched lit [] = ([], [])
-- update_watched lit (c:cls)
--   | lit_watched True lit c = 
--     case remove_watch True c of
--       Nothing -> (c : prev_ucls, prev_watched)
--       Just clause -> (prev_ucls, clause : prev_watched)
--   | lit_watched False lit c = 
--     case remove_watch False c of
--       Nothing -> (c : prev_ucls, prev_watched)
--       Just clause -> (prev_ucls, clause : prev_watched)
--   | otherwise = (prev_ucls, prev_watched)
--   where 
--     (prev_ucls, prev_watched) = update_watched lit cls

-- solve :: [String] -> [Cls] -> Maybe Subst
-- solve _ [] = Just []
-- solve optimisations clauses =
--   if (elem [] [l | l <- map literals clauses] )
--     then Nothing -- If it contains an empty clause then it is trivially unsatisfiable
--     else
--       case rho_x of 
--         Just l -> Just ((unLit cond):l)
--         Nothing -> 
--           case rho_negx of
--             Just l -> Just ((unLit (negLit cond)):l)
--             Nothing -> Nothing
--     where
--       (ucls, new_clauses) = intialize_watched clauses
--       cond  = case ucls of
--         [] -> head (literals (head new_clauses))
--         (u:uls) -> u
--       (ucls', new_clauses') = update_watched cond clauses
--       cond_x    = condition cond new_clauses'
--       cond_negx = condition (negLit cond) new_clauses;
--       rho_x     = (solve optimisations cond_x)
--       rho_negx  = (solve optimisations cond_negx)



solution :: CNF -> Maybe Subst
solution cnf =
  solve curr_clauses curr_watch alt_watch
  where
    curr_clauses = clauses cnf
    curr_watch = init_watch_aux curr_clauses
    alt_watch = true_map (all_literals cnf) (initialize_watched curr_watch)
