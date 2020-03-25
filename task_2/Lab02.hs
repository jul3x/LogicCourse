module Main where

import Control.Monad.State
import Test.QuickCheck
import Data.List
import Utils

-- ================= FROM Lab01.hs ======================

-- Variable names are just strings
type VarName = String

-- our inductive type for propositional formulas
data Formula = T | F | Var VarName | Not Formula | And Formula Formula | Or Formula Formula | Implies Formula Formula | Iff Formula Formula deriving (Eq, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, -->
(\/) = Or
(∨) = Or
(-->) = Implies

infixr 4 <-->
(<-->) = Iff

instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ (map Var ["p", "q", "r", "s", "t"]) ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f $ size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

-- finds all variables occurring in the formula (sorted, without duplicates)
variables :: Formula -> [VarName]
variables = rmdups . go where
  go T = []
  go F = []
  go (Var x) = [x]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi

-- truth valuations
type Valuation = VarName -> Bool

-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Var x) rho = rho x
eval (Not phi) rho = not $ eval phi rho
eval (And phi psi) rho = (eval phi rho) && (eval psi rho)
eval (Or phi psi) rho = (eval phi rho) || (eval psi rho)
eval (Implies phi psi) rho = not (eval phi rho) || (eval psi rho)
eval (Iff phi psi) rho = eval phi rho == eval psi rho

-- updating a truth valuation
extend :: Valuation -> VarName -> Bool -> Valuation
extend rho x v y
  | x == y = v
  | otherwise = rho y

-- the list of all valuations on a given list of variables
valuations :: [VarName] -> [Valuation]
valuations [] = [undefined] -- any initial valuation would do
valuations (x : xs) = concat [[extend rho x True, extend rho x False] | rho <- valuations xs]

-- satisfiability checker based on truth tables
satisfiable :: Formula -> Bool
satisfiable phi = or [eval phi rho | rho <- valuations (variables phi)]

-- formula simplification
simplify :: Formula -> Formula

simplify T = T
simplify F = F
simplify (Var p) = Var p

simplify (Not T) = F
simplify (Not F) = T
simplify (Not (Not phi)) = simplify phi
simplify (Not phi) = Not (simplify phi)

simplify (And T phi) = simplify phi
simplify (And phi T) = simplify phi
simplify (And F _) = F
simplify (And _ F) = F
simplify (And phi psi) = And (simplify phi) (simplify psi)

simplify (Or T _) = T
simplify (Or _ T) = T
simplify (Or F phi) = simplify phi
simplify (Or phi F) = simplify phi
simplify (Or phi psi) = Or (simplify phi) (simplify psi)

simplify (Implies T phi) = simplify phi
simplify (Implies _ T) = T
simplify (Implies F _) = T
simplify (Implies phi F) = simplify (Not phi)
simplify (Implies phi psi) = Implies (simplify phi) (simplify psi)

simplify (Iff T phi) = simplify phi
simplify (Iff phi T) = simplify phi
simplify (Iff F phi) = simplify (Not phi)
simplify (Iff phi F) = simplify (Not phi)
simplify (Iff phi psi) = Iff (simplify phi) (simplify psi)

-- keep simplifying until no more simplifications are possible
deep_simplify :: Formula -> Formula
deep_simplify phi = go where
  psi = simplify phi
  go | phi == psi = phi
     | otherwise = deep_simplify psi

-- compute the NNF (negation normal form)
nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Not T) = F
nnf (Not F) = T
nnf (Var p) = Var p
nnf (Not (Var p)) = Not $ Var p
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = nnf (Or (Not phi) psi)
nnf (Iff phi psi) = nnf (And (Implies phi psi) (Implies psi phi))
nnf (Not (Not phi)) = nnf phi
nnf (Not (And phi psi)) = nnf (Or (Not phi) (Not psi))
nnf (Not (Or phi psi)) = nnf (And (Not phi) (Not psi))
nnf (Not (Implies phi psi)) = nnf (And phi (Not psi))
nnf (Not (Iff phi psi)) = nnf (Or (And phi (Not psi)) (And (Not phi) psi))

-- data structure used in the SAT solver
data Literal = Pos VarName | Neg VarName deriving (Eq, Show, Ord)

-- compute the opposite literal
opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type SatSolver = Formula -> Bool

test_solver :: SatSolver -> Bool
test_solver solver = and $ map solver satisfiable_formulas ++ map (not . solver) unsatisfiable_formulas

-- some examples of formulas
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"

satisfiable_formulas = [p /\ q /\ s /\ p, T, p, Not p, (p \/ q /\ r) /\ (Not p \/ Not r), (p \/ q) /\ (Not p \/ Not q)]
unsatisfiable_formulas = [p /\ q /\ s /\ Not p, T /\ F, F, (p \/ q /\ r) /\ Not p /\ Not r, (p <--> q) /\ (q <--> r) /\ (r <--> s) /\ (s <--> Not p)]

-- ==================== NEW MATERIAL ===================

-- transform a formula to logically equivalent cnf (exponential complexity)
-- (entirely analogous to dnf from Lab01)
cnf :: Formula -> [[Literal]]
cnf phi = go $ nnf phi where
  go T = []
  go F = [[]]
  go (Var x) = [[Pos x]]
  go (Not (Var x)) = [[Neg x]]
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = distribute (go phi) (go psi)

-- TODO
-- transform a formula to equi-satisfiable cnf (linear complexity)
-- there is no assumption on the input formula
-- Hints:
-- - Create a fresh variable x_phi for every subformula phi.
-- - For a subformula of the form phi = phi1 op phi2, use cnf :: Formula -> [[Literal]] above to produce the cnf psi_phi of x_phi <--> x_phi1 op x_phi2
-- - Concatenate all the cnfs psi_phi for every subformula phi.
-- - See slide #5 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
ecnf :: Formula -> [[Literal]]
ecnf phi = result ++ [[Pos ("x_phi" ++ show var)]] where
  (result, var) = go phi 0 where
  go (Or phi psi) y = (left_res ++ right_res ++ 
                       cnf (Iff (Var ("x_phi" ++ show (right_var + 1))) (Or (Var ("x_phi" ++ show (left_var))) (Var ("x_phi" ++ show (right_var))))), 
                       right_var + 1) 
    where (left_res, left_var) = go phi y
          (right_res, right_var) = go psi left_var
  go (And phi psi) y = (left_res ++ right_res ++ 
                        cnf (Iff (Var ("x_phi" ++ show (right_var + 1))) (And (Var ("x_phi" ++ show (left_var))) (Var ("x_phi" ++ show (right_var))))), 
                        right_var + 1) 
    where (left_res, left_var) = go phi y
          (right_res, right_var) = go psi left_var
  go (Iff phi psi) y = (left_res ++ right_res ++ 
                       cnf (Iff (Var ("x_phi" ++ show (right_var + 1))) (Iff (Var ("x_phi" ++ show (left_var))) (Var ("x_phi" ++ show (right_var))))), 
                       right_var + 1) 
    where (left_res, left_var) = go phi y
          (right_res, right_var) = go psi left_var
  go (Implies phi psi) y = (left_res ++ right_res ++ 
                            cnf (Iff (Var ("x_phi" ++ show (right_var + 1))) (Implies (Var ("x_phi" ++ show (left_var))) (Var ("x_phi" ++ show (right_var))))), 
                            right_var + 1) 
    where (left_res, left_var) = go phi y
          (right_res, right_var) = go psi left_var
  go (Not phi) y = (left_res ++ 
                            cnf (Iff (Var ("x_phi" ++ show (left_var + 1))) (Not (Var ("x_phi" ++ show (left_var))) )), left_var+1) 
    where (left_res, left_var) = go phi y
  go x y = (cnf (Iff (Var ("x_phi" ++ show (y+1))) x), y+1)
      

equi_satisfiable :: Formula -> Formula -> Bool
equi_satisfiable phi psi = satisfiable phi == satisfiable psi

-- convert a CNF in the list of clauses form to a formula
-- entirely analogous to "dnf2formula" from Lab01
cnf2formula :: [[Literal]] -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos x) = Var x
  go2 (Neg x) = Not (Var x)

-- test for ecnf
prop_ecnf :: Formula -> Bool
prop_ecnf phi = equi_satisfiable phi (cnf2formula $ ecnf phi)

-- TODO
-- RESOLUTION
-- Apply the resolution rule by picking a variable appearing both positively and negatively.
-- Perform all possible resolution steps involving this variable in parallel.
-- Add all the resulting clauses (resolvents) and remove all clauses involving the selected variable.
-- See slide #15, point 6 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf

-- Assumption 1: every variable appears positively and negatively
-- Assumption 2: no variable appears both positively and negatively in the same clause (tautology)
-- Assumption 3: there is at least one clause
-- Assumption 4: all clauses are nonempty

-- takes all of the clauses where VarName "name" appears negatively
all_negative name lss =  map (\z -> filter (/= Neg name) z) (filter (\clause -> (Neg name) `elem` clause) lss)
-- takes all of the clauses where VarName "name" appears positively
all_positive name lss =  map (\z -> filter (/= Pos name) z) (filter (\clause -> (Pos name) `elem` clause) lss)
-- takes all of the others clauses
others name lss = filter (\clause -> not ((Pos name) `elem` clause || (Neg name) `elem` clause)) lss

resolution :: [[Literal]] -> [[Literal]]
resolution lss = resolution' lss (variables (cnf2formula lss))

resolution' lss [] = lss
resolution' lss (name:names) 
  | length all_negative' > 0 && length all_positive' > 0 = resolution' ((distribute all_positive' all_negative') ++ (others name lss)) []
  | otherwise = resolution' lss names
  where all_negative' = all_negative name lss
        all_positive' = all_positive name lss
        others' = others name lss

prop_resolution :: Bool
prop_resolution = resolution [[Pos "p", Pos "q"], [Neg "p", Neg "q"]] == [[Pos "q", Neg "q"]]

-- find all positive occurrences of a variable name
positive_literals :: [Literal] -> [VarName]
positive_literals ls = rmdups [p | Pos p <- ls]

-- find all negative occurrences of a variable name
negative_literals :: [Literal] -> [VarName]
negative_literals ls = rmdups [p | Neg p <- ls]

-- find all occurrences of a variable name
literals :: [Literal] -> [VarName]
literals ls = rmdups $ positive_literals ls ++ negative_literals ls

-- TODO
-- remove clauses containing a positive and a negative occurrence of the same literal

compareList :: (Eq a) => [a] -> [a] -> Bool
compareList a = null . intersect a

remove_tautologies :: [[Literal]] -> [[Literal]]
remove_tautologies lss = filter (\x -> compareList (negative_literals x) (positive_literals x)) lss

prop_remove_tautologies =
    remove_tautologies [[Pos "p", Pos "x", Neg "p"], [Pos "x", Pos "y"], [Pos "p", Neg "q"]] == [[Pos "x", Pos "y"], [Pos "p", Neg "q"]]

-- TODO
-- One literal rule (aka unit propagation):
-- A one-literal clause [... [l] ...] can be removed
-- Hint: Remove [l] and all clauses containing l
-- Hint: Remove all occurrences of "opposite l"
-- Hint: If any empty clause [... [] ...] arises from this process then this is UNSAT
-- see slide #6 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf

one_literal :: [[Literal]] -> [[Literal]]
one_literal lss = one_literal' lss []

removeL l xs = filter (\y -> not (l `elem` y)) xs

removeOpposite l xs = map (\z -> filter (/= opposite l) z) xs

one_literal' [] done = done
one_literal' ([x]:xs) done = one_literal' (removeOpposite x (removeL x xs)) (removeOpposite x (removeL x done))
one_literal' (x:xs) done = one_literal' xs (x:done)

-- correctness test
prop_one_literal :: Bool
prop_one_literal =
  one_literal [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]] ==
    [[Neg "q",Pos "r",Neg "r"],[Neg "q"],[Pos "q",Pos "r",Pos "s"]] &&
  one_literal [[Pos "p2"],[Neg "p2",Pos "p"],[Neg "p2",Pos "p1"],[Neg "p",Neg "p1",Pos "p2"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  one_literal [[Pos "q"],[Pos "p0"],[Neg "p0",Pos "s"],[Neg "p0"]] ==
    [[]]

-- TODO
-- Affirmative-negative rule (aka elimination of pure literals)
-- Remove all clauses containing a literal that appears only positively or negatively in every clause
-- see slide #7 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
-- this is the same as "elimination of pure literals" from the slide

get_all_positive_literals lls = rmdups (get_all_positive_literals' lls)
get_all_positive_literals' [] = []
get_all_positive_literals' (x:xs) = positive_literals x ++ get_all_positive_literals' xs

get_all_negative_literals lls = rmdups (get_all_negative_literals' lls)
get_all_negative_literals' [] = []
get_all_negative_literals' (x:xs) = negative_literals x ++ get_all_negative_literals' xs

get_all_pure_literals lls = (neg \\ pos) ++ (pos \\ neg)
  where neg = get_all_negative_literals lls
        pos = get_all_positive_literals lls

affirmative_negative :: [[Literal]] -> [[Literal]]
affirmative_negative lss = affirmative_negative' lss (get_all_pure_literals lss)

affirmative_negative' lss [] = lss
affirmative_negative' lss (l:ls) = affirmative_negative' (filter (\clause -> not ((Neg l) `elem` clause || (Pos l) `elem` clause)) lss) ls

prop_affirmative_negative :: Bool
prop_affirmative_negative =
  affirmative_negative [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
                       [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  affirmative_negative [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Pos "p"],[Neg "s",Pos "p",Pos "p0"]] ==
                       [[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"]]

-- the main DP satisfiability loop
-- this implements #15 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
loop_DP :: [[Literal]] -> Bool
loop_DP [] = True -- if the CNF is empty, then it is satisfiable
loop_DP lss | elem [] lss = False -- if there is an empty clause, then the CNF is not satisfiable
loop_DP lss =
  -- apply one round of simplification by removing tautologies, applying the one-literal rule, and the affirmative_negative rule
  let lss' = rmdups . map rmdups . affirmative_negative . one_literal . remove_tautologies $ lss in
    if lss == lss'
      -- if the CNF didn't change, then do a resolution step (expensive)
      then loop_DP $ resolution lss
      -- if the CNF didn change, then do another round of simplifications recursively
      else loop_DP lss'

-- the DP SAT solver
sat_DP :: SatSolver
sat_DP = loop_DP . ecnf . deep_simplify 

-- tests on random formulas
prop_DP :: Formula -> Bool
prop_DP phi = (print phi) `seq`
  sat_DP phi == satisfiable phi

-- tests on fixed formulas
prop_DP2 :: Bool
prop_DP2 = test_solver sat_DP

main = do 
  quickCheckWith (stdArgs {maxSize = 5}) prop_ecnf
  quickCheck prop_one_literal
  quickCheck prop_resolution
  quickCheck prop_affirmative_negative
  quickCheck prop_remove_tautologies
  quickCheckWith (stdArgs {maxSize = 10}) prop_DP
  quickCheck prop_DP2