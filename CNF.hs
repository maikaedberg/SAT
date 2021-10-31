-- types of CNF formulas and substitutions
module CNF where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

type Var = Int
--data Lit = Lit    { var :: Var , pol :: Bool }                 deriving (Ord,Show,Eq)
--data Cls = BigOr  { literals :: Set Lit }                        deriving (Show,Eq)
--data CNF = BigAnd { vars :: Set Var, clauses  :: Set Cls }         deriving (Show,Eq)
data Lit = Lit    { var :: Var , pol :: Bool, set :: Bool }                 deriving (Ord,Show)
data Cls = BigOr  { literals :: [Lit], index :: Int}                        deriving (Show,Eq)
data CNF = BigAnd { vars :: [Var], clauses  :: [Cls] }         deriving (Show,Eq)

instance Eq Lit where
  (==) (Lit v1 p1 _) (Lit v2 p2 _) = (v1 == v2) && (p1 == p2)
  
--type Subst = Set (Var,Bool)
type Subst =  [(Var,Bool)]

-- destructor extracting a variable/boolean pair from a literal
unLit :: Lit -> (Var,Bool)
unLit (Lit v b a) = (v,b)

negLit :: Lit -> Lit
negLit (Lit v b a) = (Lit v (not b) a)

-- some pretty printing routines

prettyLit :: Lit -> String
prettyLit (Lit v b a) = (if b then "" else "-") ++ "x" ++ show v

prettyCls :: Cls -> String
--prettyCls = Data.List.intercalate " | " .  toList . Data.Set.map prettyLit . literals
prettyCls = intercalate " | " . map prettyLit . literals


prettyCNF :: CNF -> String
prettyCNF = intercalate " & " . map (parens . prettyCls) . clauses
--prettyCNF = Data.List.intercalate " & " . toList . Data.Set.map (parens . prettyCls) . clauses
  where
    parens :: String -> String
    parens s = "(" ++ s ++ ")"

-- measuring the size of formulas in terms of clauses and literals

numClss :: CNF -> Int
numClss = length . clauses

numLits :: CNF -> Int
--numLits = sum . Data.Set.map (length . literals) . clauses
numLits = sum . map (length . literals) . clauses

clauseLits :: [Cls] -> [Lit]
clauseLits [] = []
clauseLits (c:cls) = 
  [l | l <- literals c, not (elem l prev)] ++ prev
  where
    prev = clauseLits cls

all_literals :: CNF -> [Lit]
all_literals (BigAnd [] _) = []
all_literals (BigAnd (v:vars) c) = 
  [lit, negLit lit] ++ (all_literals (BigAnd vars c))
  where
    lit = Lit v True False
