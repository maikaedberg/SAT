-- types of CNF formulas and substitutions
module CNF where

import Data.List

type Var = Int
data Lit = Lit    { var :: Var , pol :: Bool }                 deriving (Ord,Show,Eq)
data Cls = BigOr  { literals :: [Lit] }                        deriving (Show,Eq)
data CNF = BigAnd { vars :: [Var], clauses  :: [Cls] }         deriving (Show,Eq)

type Subst = [(Var,Bool)]

-- destructor extracting a variable/boolean pair from a literal
unLit :: Lit -> (Var,Bool)
unLit (Lit v b) = (v,b)

negLit :: Lit -> Lit
negLit (Lit v b) = (Lit v (not b))

-- some pretty printing routines

prettyLit :: Lit -> String
prettyLit (Lit v b) = (if b then "" else "-") ++ "x" ++ show v

prettyCls :: Cls -> String
prettyCls = intercalate " | " . map prettyLit . literals

prettyCNF :: CNF -> String
prettyCNF = intercalate " & " . map (parens . prettyCls) . clauses
  where
    parens :: String -> String
    parens s = "(" ++ s ++ ")"

-- measuring the size of formulas in terms of clauses and literals

numClss :: CNF -> Int
numClss = length . clauses

numLits :: CNF -> Int
numLits = sum . map (length . literals) . clauses

