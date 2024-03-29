-- evaluation of CNF formulas under a substitution
module CNF.Eval where

import CNF
import Data.Set (Set)
import qualified Data.Set as Set

evalLit :: Subst -> Lit -> Bool
evalCls :: Subst -> Cls -> Bool
evalCNF :: Subst -> CNF -> Bool

lookupVar :: Subst -> Var -> Bool
lookupVar rho x = case lookup x rho of
--lookupVar rho x = case lookup x (Set.toList rho) of
                    Nothing -> error ("lookupVar: " ++ show x ++ " not in substitution")
                    Just b -> b


evalLit rho x = (if pol x then id else not) $ lookupVar rho (var x)
--evalCls rho = or . Set.map (evalLit rho) . literals
--evalCNF rho = and . Set.map (evalCls rho) . clauses
evalCls rho = or . map (evalLit rho) . literals
evalCNF rho = and . map (evalCls rho) . clauses
