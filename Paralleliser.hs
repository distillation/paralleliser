module Paralleliser where

import Language.Core
import Data.List(intersect, nub)
import Data.Char(isLower)
import Partitioner

import qualified Language.Haskell.Exts as LHE

isDistilledExpression :: Term -> Bool
isDistilledExpression (Free _) = True
isDistilledExpression (Bound _) = True
isDistilledExpression (Con _ []) = True
isDistilledExpression (Con _ es) = all isDistilledExpression es
isDistilledExpression (Apply e (Free _)) = isDistilledExpression e
isDistilledExpression (Apply e (Bound _)) = isDistilledExpression e
isDistilledExpression (Apply e (Fun _)) = isDistilledExpression e
isDistilledExpression (Fun _) = True
isDistilledExpression (Lambda _ e) = isDistilledExpression e
isDistilledExpression (Let _ e e') = isDistilledExpression e && isDistilledExpression e'
isDistilledExpression (Where e es) = isDistilledExpression e && all (isDistilledExpression . snd) es
isDistilledExpression (Case (Free _) bs) = all isDistilledBranch bs
isDistilledExpression (Case (Bound _) bs) = all isDistilledBranch bs
isDistilledExpression (Case (Fun _) bs) = all isDistilledBranch bs
isDistilledExpression (TupleLet _ e e') = isDistilledExpression e && isDistilledExpression e'
isDistilledExpression (Tuple es) = all isDistilledExpression es
isDistilledExpression _ = False

isDistilledBranch :: Branch -> Bool
isDistilledBranch (Branch _ _ e) = isDistilledExpression e

parallelize :: Term -> [Int] -> Term
parallelize (Free v) p = Free v
parallelize (Bound i) p = Bound i
parallelize (Con c es) p = Con c (map (\e -> parallelize e p) es)
parallelize (Apply e (Bound i)) p = Apply (parallelize e p) (Bound i)
parallelize (Apply e (Free x)) p = Apply (parallelize e p) (Free x)
parallelize (Fun f) p = Fun f
parallelize (Lambda x e) p = Lambda x (parallelize e (map (+1) p))
parallelize (Where e fs) p = Where (parallelize e p) (map (\(n, b) -> (n, parallelize b p)) fs)
parallelize (Case (Free x) bs) p = Case (Free x) (map (\b -> parallelizeBranch b p) bs)
parallelize (Case (Bound i) bs) p = Case (Bound i) (map (\b -> parallelizeBranch b p) bs)
parallelize (Case (Fun f) bs) p = Case (Fun f) (map (\b -> parallelizeBranch b p) bs)
parallelize (Tuple es) p = Tuple (map (\e -> parallelize e p) es)
parallelize (Let x e e') p
 | length intersect_e > 0 && length intersect_e' > 0 = Let x (parallelize e p) (Apply (Apply (Fun "par") (Apply (Fun "rdeepseq") (Bound 0))) (parallelize e' (map (+1) p)))
 | length intersect_e > 0 && length intersect_e' == 0 = Let x (parallelize e p) (Apply (Apply (Fun "pseq") (Bound 0)) (parallelize e' []))
 | otherwise = Let x (parallelize e p) (parallelize e' p)
 where
     intersect_e = intersect (bound e) p
     intersect_e' = intersect (bound e') (map (+1) p)
parallelize (TupleLet xs e e') p = TupleLet xs e e'

parallelizeBranch :: Branch -> [Int] -> Branch   
parallelizeBranch (Branch "Join" args@(x:x':x'':[]) e) p = Branch "Join" args (parallelize e (nub (0:1:map (+2) p)))
parallelizeBranch (Branch c args e) p = Branch c args (parallelize e (map (+ (length args)) p))

parallelizeFunction :: Function -> Function
parallelizeFunction (n, e) = (n, parallelizeTerm e)

parallelizeTerm :: Term -> Term
parallelizeTerm e = parallelize e []

parallelizeProgram :: Program -> Program
parallelizeProgram (Program t c m p w e i) = Program (parallelizeTerm t) c m p w e i

monomorphismPragma :: LHE.ModulePragma
monomorphismPragma = LHE.LanguagePragma (LHE.SrcLoc "" 0 0) [LHE.Ident "NoMonomorphismRestriction"]

parallelizeFile :: FilePath -> IO Program
parallelizeFile file = do
    Program t c m p w e i <- parseFile file
    let Program t' c' m' p' w' e' i' = parallelizeProgram (Program t (c ++ generateFlattenedDataTypes c) m p w e i)
    return (Program (Where t' (generatePartitioningFunctions c ++ generateRebuildingFunctions c)) c' m' (monomorphismPragma:p')  w' e' i')
    
bound :: Term -> [BoundVar]
bound = bound' 0 []

{-|
    Given a 'Term', returns the set of 'BoundVar's within that 'Term' combined with a supplied set of 'BoundVar's.
-}

bound' :: Int -> [BoundVar] -> Term -> [BoundVar]
bound' _ bs (Free _) = bs
bound' d bs (Bound i)
 | b < 0 || b `elem` bs = bs
 | otherwise = b:bs
 where b = i - d
bound' d bs (Lambda _ t) = bound' (d + 1) bs t
bound' d bs (Con _ ts) = foldr (flip (bound' d)) bs ts
bound' d bs (Apply t u) = bound' d (bound' d bs u) t
bound' _ bs (Fun _) = bs
bound' d bs (Case t bs') = foldr (\(Branch _ xs t') bs'' -> bound' (d + length xs) bs'' t') (bound' d bs t) bs'
bound' d bs (Let _ t u) = bound' (d + 1) (bound' d bs t) u
bound' d bs (Where t ds) = bound' d (foldr (\(_, t') bs' -> bound' d bs' t') bs ds) t
bound' d bs (Tuple es) = foldr (\e bs' -> bound' d bs' e) bs es
bound' d bs (TupleLet xs t u) = bound' (d + length xs) (bound' d bs t) u