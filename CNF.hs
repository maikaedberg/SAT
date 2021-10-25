-- types of CNF formulas and substitutions
module CNF where

import Data.List
--import Data.Set 

type Var = Int
--data Lit = Lit    { var :: Var , pol :: Bool }                 deriving (Ord,Show,Eq)
--data Cls = BigOr  { literals :: Set Lit }                        deriving (Show,Eq)
--data CNF = BigAnd { vars :: Set Var, clauses  :: Set Cls }         deriving (Show,Eq)
data Lit = Lit    { var :: Var , pol :: Bool }                 deriving (Ord,Show,Eq)
data Cls = BigOr  { literals :: [Lit] }                        deriving (Show,Eq)
data CNF = BigAnd { vars :: [Var], clauses  :: [Cls] }         deriving (Show,Eq)

--type Subst = Set (Var,Bool)
type Subst =  [(Var,Bool)]

-- destructor extracting a variable/boolean pair from a literal
unLit :: Lit -> (Var,Bool)
unLit (Lit v b) = (v,b)

negLit :: Lit -> Lit
negLit (Lit v b) = (Lit v (not b))

-- some pretty printing routines

prettyLit :: Lit -> String
prettyLit (Lit v b) = (if b then "" else "-") ++ "x" ++ show v

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
