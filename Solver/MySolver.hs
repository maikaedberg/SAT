module Solver.MySolver (solution, cnfTo3CNF) where

import CNF
import CNF.Eval

import Data.List
import Data.Maybe
import Data.Bits
import qualified Data.Map as Map
import qualified Data.Set as Set

fill :: [Var] -> Subst -> Subst
fill []     subst = subst
fill (v:vars) subst =
  if v `elem` map fst subst
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
    | elem (negLit l) (literals c) = Just (BigOr (filter (/= negLit l) (literals c))) -- neg literal found in clause
    | otherwise                    = Just c

condition :: Lit -> [Cls] -> [Cls]
condition l [] = []
condition l (c:cs) =
    case filterLit l c of
        Nothing -> condition l cs
        Just filtered ->  filtered:(condition l cs)

-- Assuming that every element in the sublist is unique
subList :: Eq a => [a] -> [a] -> Bool
subList xs ys = foldr (\x y -> y && x `elem` ys) True xs

computeSignature :: Cls -> Int
computeSignature (BigOr lits) = foldr (.|.) 0 [var lit | lit <- lits]

subset :: Cls -> Cls -> Bool
subset cls1 cls2 =  computeSignature cls1 .&. complement (computeSignature cls2) == 0 && subList (literals cls1) (literals cls2)

findSmallestOccur :: Map.Map Lit [Cls] -> Cls -> Lit
findSmallestOccur occur (BigOr [])     = error "Called findSmallestOccur on empty list"
findSmallestOccur occur (BigOr [l])    = l
findSmallestOccur occur (BigOr (l:ls)) = case Map.lookup l occur of
  Nothing -> error "literal does not occur in any clause"
  Just clause -> case Map.lookup prevL occur of
    Nothing      -> error "literal does not occur in any clause"
    Just prevCls ->  if length clause > length prevCls then l else prevL
  where
    prevL =  findSmallestOccur occur (BigOr ls)

findSubsumed :: Map.Map Lit [Cls] -> Cls -> [Cls]
findSubsumed occurs (BigOr []) = []
findSubsumed occurs cls        = case Map.lookup (findSmallestOccur occurs cls) occurs of
  Nothing -> error "literal does not occur in any clause"
  Just clauses -> [clause | clause <- clauses,
                            clause /= cls,
                            length (literals clause) <= lenCls,
                            subset clause cls]
  where
    lenCls = length (literals cls)

selfSubsume :: Map.Map Lit [Cls] -> Cls -> (Cls, [(Cls, Lit)])
selfSubsume occurs cls = (cls, concat [toStrenghten p | p <- literals cls]) where
  toStrenghten p = [(cls', pNeg) | cls' <- subsumed] where
    pNeg     = negLit p
    clsNeg   = BigOr [ if lit /= p then lit else pNeg | lit <- literals cls]
    subsumed = findSubsumed occurs clsNeg

updateMap :: Cls -> Cls -> Map.Map Lit [Cls] -> Map.Map Lit [Cls]
updateMap (BigOr []) c occurs     = occurs
updateMap (BigOr (l:ls)) c occurs = case Map.lookup l occurs of
  Nothing  -> Map.insert l [c] occurs
  Just cls -> Map.insert l (c:cls) occurs

buildOccurs :: CNF -> Map.Map Lit [Cls]
buildOccurs (BigAnd vars [])      = Map.empty
buildOccurs (BigAnd vars (c:cls)) = updateMap c c (buildOccurs (BigAnd vars cls))

preprocess :: [Cls] -> [Cls]
preprocess [] = []
preprocess (c:cs)
  | elem True [subList y (literals c) | y <- (map literals cs)] = preprocess cs
  | otherwise                         = c:(preprocess cs)

removeLit :: Cls -> Lit -> Cls
removeLit clause lit = BigOr [l | l <- literals clause, l /= lit]

strengthenClause :: [Cls] -> (Cls,[(Cls, Lit)]) -> [Cls]
strengthenClause clauses (ogCls, [])           = clauses
strengthenClause clauses (ogCls, (c, lit):cls) = [if clause == c then removeLit clause lit else clause | clause <- clauses, clause /= ogCls]

strengthenClauses :: [Cls] -> [(Cls,[(Cls, Lit)])] -> [Cls]
strengthenClauses clauses []         = clauses 
strengthenClauses clauses [cl]       = strengthenClause clauses cl
strengthenClauses clauses (cl : cls) = strengthenClauses (strengthenClause clauses cl) cls

subsumptionAux2 :: Map.Map Lit [Cls] -> [Cls] -> [(Cls,[(Cls, Lit)])]
subsumptionAux2 occurs = map (selfSubsume occurs)

subsumptionAux :: [Var] -> Map.Map Lit [Cls] -> Lit -> [Cls] -> [Cls] -> [Cls] -> [Cls]
subsumptionAux [] occurs firstLit s1 clauses strengthened   = clauses
subsumptionAux vars occurs firtsLit s1 clauses []           = clauses
subsumptionAux (v:vars) occurs firstLit s1 clauses strengthened = subsumptionAux vars occurs newFirstLit newS1 newClauses newStrengthened where
  toStrengthen    = case subsumptionAux2 occurs s1 of
    [] -> []
    toStrengthenTemp -> subsumptionAux2 occurs newS1 where
      firstLitNeg = negLit firstLit
      clauses     = strengthenClauses clauses toStrengthenTemp
      newTempS1   = [cls | cls <- clauses, firstLitNeg `elem` literals cls]
      newS1       = map fst toStrengthenTemp `union` newTempS1
  newClauses      = strengthenClauses clauses toStrengthen
  newStrengthened = nub (map fst (concatMap snd toStrengthen))
  newFirstLit     = Lit v True
  negFirstLit     = negLit newFirstLit
  newTempS1       = [cls | cls <- newClauses, negFirstLit `elem` literals cls] 
  newS1           = newTempS1 `union` newStrengthened

subsumption :: CNF -> CNF
subsumption (BigAnd vars clauses) = BigAnd vars (subsumptionAux (tail vars) occurs firstLit s1 clauses strengthened) where
  touched      = Set.fromList vars
  strengthened = []
  occurs       = buildOccurs (BigAnd vars clauses)
  firstLit     = case vars of
    []       -> error "No variables"
    otheriwse -> Lit (head vars) True
  firstLitNeg  = negLit firstLit
  s0           = [cls | cls <- clauses, firstLit `elem` literals cls]
  s1           = clauses
  toStrengthen = [selfSubsume occurs c | c <- s1]

newVar :: [Var] -> Var
newVar = foldr (\v -> max (v+1) ) 1

initNewVars :: Int -> [Var] -> [Var]
initNewVars n vars = [minNewVar..(minNewVar + n)] where
  minNewVar = newVar vars

createClauses :: Int -> [Var] -> Cls -> [Cls]
createClauses 0 newvars oldClause = [BigOr [l1, l2, z]] where
  lits = literals oldClause
  lenOC = length lits
  l1 = lits!!(lenOC - 2)
  l2 = last lits
  z = Lit (last newvars) True
createClauses k newvars oldClause = BigOr [l, z1, z2] : createClauses (k-1) newvars oldClause where
  lits = literals oldClause
  lenOC = length lits
  l = lits!!(lenOC - (k+3))
  z1 = Lit (newvars!!(lenOC - (k+1))) False
  z2 = Lit (newvars!!(lenOC - (k+2))) True

mapSecond :: (a -> b) -> (c, a) -> (c, b)
mapSecond f (c, a) = (c, f a)

cnfTo3CNF_aux :: [Var] -> [Cls] -> ([Var], [Cls])
cnfTo3CNF_aux vars []      = (vars, [])
cnfTo3CNF_aux vars (c:cls)
  | k == 0 = (vars, [c]) -- If there is a clause of length 0 then the CNF is unsatisfiable 
  | k <= 3 = mapSecond (c:) (cnfTo3CNF_aux vars cls)
  | k > 3  = (newVars, newClauses) where
    clause      = literals c
    k           = length clause
    newVarList  = initNewVars (k - 3) vars
    c1          = BigOr (take 2 clause ++ [Lit (head newVarList) True])
    clauses     = c1 : createClauses (k - 4) newVarList c
    updatedVars = newVarList ++ vars
    res         = cnfTo3CNF_aux updatedVars cls
    newVars     = fst res
    newClauses  = clauses ++ snd res

cnfTo3CNF :: CNF -> CNF
cnfTo3CNF (BigAnd vars clauses) = BigAnd newvars newclauses where
  res        = cnfTo3CNF_aux vars clauses
  newvars    = fst res
  newclauses = snd res

solution :: [String] -> CNF -> Maybe Subst
solution optimisations cnf =
  case solve optimisations (clauses cnf'') of
    Nothing -> Nothing
    Just sub -> Just (fill (vars cnf'') sub)
  where
    cnf' =
      case elem "-ss" optimisations of
        True -> subsumption cnf
        False -> cnf
    cnf'' =
      case elem "-3cnf" optimisations of
        True -> cnfTo3CNF cnf'
        False -> cnf'
