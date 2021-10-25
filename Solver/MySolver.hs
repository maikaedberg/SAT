module Solver.MySolver (solution, cnfTo3CNF) where

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

find_uc :: [Cls] -> [Cls] -> ([Cls], Bool)
-- looks for a unit clause 
-- returns unit clause at the head of the list if found
-- othewrise return what was given initally
find_uc [] accum_cls = (accum_cls, False)
find_uc (c:cls) accum_cls
  | (length (literals c)) == 1 = (c:(accum_cls ++ cls), True)
  | otherwise                  = find_uc cls (c:accum_cls)
   
solve_uc :: [Cls] -> Maybe Subst
solve_uc [] = Just []
solve_uc clauses =
  if (elem ( BigOr [] ) clauses)
    then Nothing -- If it contains an empty clause then it is trivially unsatisfiable,
    else
      case rho_x of 
        Just l -> Just ((unLit cond):l)
        Nothing -> 
          case rho_negx of
            Just l -> Just ((unLit (negLit cond)):l)
            Nothing -> Nothing
    where
      (new_clauses, found_uc) = find_uc clauses []
      cond      = head (literals (head new_clauses))
      cond_x    = condition cond new_clauses
      cond_negx = condition (negLit cond) new_clauses
      rho_x     = (solve_uc cond_x)
      rho_negx  = 
        case found_uc of
          True -> Nothing
          False ->  (solve_uc cond_negx)


neg_lit_in :: Lit -> [Cls] -> Bool
-- returns True if the negation of the literal is in one of the clauses
--         False otherwise
neg_lit_in lit [] = False
neg_lit_in lit (c:clauses) = (elem (negLit lit) (literals c)) || (neg_lit_in lit clauses)

solve_uc_le :: [Cls] -> Maybe Subst
solve_uc_le [] = Just []
solve_uc_le clauses =
  if (elem ( BigOr [] ) clauses)
    then Nothing -- If it contains an empty clause then it is trivially unsatisfiable,
    else
      case rho_x of 
        Just l -> Just ((unLit cond):l)
        Nothing -> 
          case rho_negx of
            Just l -> Just ((unLit (negLit cond)):l)
            Nothing -> Nothing
    where
      (new_clauses, found_uc) = find_uc clauses []
      cond      = head (literals (head new_clauses))
      found_neg_lit  = neg_lit_in cond new_clauses
      cond_x    = condition cond new_clauses
      cond_negx = condition (negLit cond) new_clauses
      rho_x     = (solve_uc_le cond_x)
      rho_negx  = 
        case found_uc of
          True -> Nothing
          False -> 
            case found_neg_lit of
              True -> (solve_uc_le cond_negx)
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
  case solve_uc_le (clauses cnf) of
    Nothing -> Nothing
    Just sub -> Just (fill (vars cnf') sub) where 
      cnf' = cnfTo3CNF cnf

newVar :: [Var] -> Var
newVar = foldr (\v -> max (v+1) ) 1 

initNewVars :: Int -> [Var] -> [Var]
initNewVars n vars = [minNewVar..(minNewVar + n)] where 
  minNewVar = newVar vars

createClauses :: Int -> [Var] -> [Var] -> Cls -> [Cls]
createClauses 0 vars newvars oldClause = [BigOr [l1, l2, z]] where
  lits = literals oldClause
  lenOC = length lits
  l1 = lits!!(lenOC - 2)
  l2 = last lits 
  z = Lit (last newvars) True
createClauses k vars newvars oldClause = BigOr [l, z1, z2] : createClauses (k-1) vars newvars oldClause where 
  lits = literals oldClause 
  lenOC = length lits 
  l = lits!!(lenOC - (k+3))
  z1 = Lit (newvars!!(lenOC - (k+1))) False
  z2 = Lit (newvars!!(lenOC - (k+2))) True

cnfTo3CNF_aux :: [Var] -> [Cls] -> ([Var], [Cls])
cnfTo3CNF_aux vars []      = (vars, [])
cnfTo3CNF_aux vars (c:cls) = case length (literals c) of
  0 -> (vars, c:cls) -- If there is a clause of length 0 then the CNF is unsatisfiable 
  1 -> (newVars, newClauses) where 
    newVarList  = initNewVars 2 vars
    updatedVars = newVarList ++ vars
    res         = cnfTo3CNF_aux updatedVars cls
    newVars     = fst res
    newLit1     = Lit (head newVarList) True 
    newLit2     = Lit (newVarList!!1) True
    newClauses  = BigOr ([newLit1, newLit2] ++ literals c) : snd res
  2 -> (newVars, newClauses) where 
    newVar1     = newVar vars
    updatedVars = newVar1 : vars 
    res         = cnfTo3CNF_aux vars cls 
    newVars     = fst res
    newLit1     = Lit newVar1 True 
    newClauses  = BigOr (newLit1 : literals c) : snd res
  3 -> (newVars, c:newClauses) where 
    res        = cnfTo3CNF_aux vars cls
    newVars    = fst res
    newClauses = snd res
  otherwise -> (newVars, newClauses) where 
    k = length (literals c)
    newVarList  = initNewVars (k - 3) vars 
    clause      = literals c 
    c1          = BigOr (take 2 clause ++ [Lit (head newVarList) True])
    clauses     = c1 : createClauses (k - 4) vars newVarList c
    updatedVars = newVarList ++ vars
    res         = cnfTo3CNF_aux updatedVars cls
    newVars     = fst res
    newClauses  = clauses ++ snd res

cnfTo3CNF :: CNF -> CNF
cnfTo3CNF (BigAnd vars clauses) = BigAnd newvars newclauses where
  res        = cnfTo3CNF_aux vars clauses
  newvars    = fst res
  newclauses = snd res


-- check for correctness + performance

solution_subsumption :: CNF -> Maybe Subst
solution_subsumption cnf = 
  case solve (clauses cnf') of
    Nothing -> Nothing
    Just sub -> do
            Just (fill (vars cnf') sub)
  where
    cnf' = subsumption cnf

