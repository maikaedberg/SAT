module Solver.MySolver (solution) where

import CNF
import CNF.Eval

import Data.List
import Data.Maybe

solve :: [Cls] -> Maybe Subst
solve [] = return []
solve (c:clauses)
    | length cond_x > 0   = do
            rho <- solve cond_x
            return ((unLit cond):rho)
    | length cond_negx > 0 = do
            rho <- solve cond_negx
            return ((unLit (negLit cond)):rho)
    | otherwise            = Nothing
    where
        cond      = head (literals c)
        cond_x    = condition cond (c:clauses)
        cond_negx = condition (negLit cond) (c:clauses)

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

solution :: CNF -> Maybe Subst
solution cnf = solve (clauses cnf)
