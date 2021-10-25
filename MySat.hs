import CNF
import CNF.DIMACS
import qualified CNF.Eval as Eval

--import qualified Solver.Naive as Naive
import qualified Solver.MySolver as MySolver

import Control.Monad
import System.Environment
import System.Exit

expected_flags :: [String] -> [String] -> Bool
expected_flags opts [] = True
expected_flags opts (a:args) = elem a opts && expected_flags opts args

main :: IO ()
main = do
  name <- getProgName
  args <- getArgs
  unless (length args >= 1) $ do
    putStrLn ("Usage: " ++ name ++ " <cnf file>")
    exitFailure
  unless (drop (length (args !! 0) - 4) (args !! 0) == ".cnf") $ do
    putStrLn ("Usage: " ++ name ++ " <cnf file>")
    exitFailure
  unless (expected_flags ["-ss", "-up", "-ple", "-greedy"] (tail args))$ do
    putStrLn ("Unrecognised flag!\n" ++
              "The current optimisations supported are: \n" ++
              "\tsubsumption (-ss)\n" ++ 
              "\tunit propogation (-up)\n" ++
              "\tpure literal elimination (-ple)")
    exitFailure
  f <- readCNFfromDIMACS (args !! 0)
  --case Naive.solution f of
  --  Nothing  -> putStrLn "UNSAT"
  --  Just rho -> putStrLn ("NAIVE SAT\n" ++ dimacsSubst rho)
  case MySolver.solution (tail args) f of
    Nothing  -> putStrLn "UNSAT"
    Just rho -> putStrLn ("MY SAT\n" ++ dimacsSubst rho ++ sol_right)
      where 
        sol_right = 
          case Eval.evalCNF rho f of
            False -> "\nYour solution is incorrect"
            True  -> "\nYour solution is correct"
