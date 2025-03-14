module Project (prove, proveCount) where

import Sequent
import Data.List (nub, delete)

type Rule = Sequent -> Maybe [Sequent]

-- Helper function to find a proposition with a given main connective
findMainConnective :: (Prop -> Maybe Prop) -> [Prop] -> Maybe (Prop, [Prop])
findMainConnective pred props = case foldr checkProp Nothing props of
    Just p -> Just (p, delete p props)
    Nothing -> Nothing
  where
    checkProp p Nothing = pred p >>= \matched -> Just matched
    checkProp _ found = found

-- Helper functions to check for specific connectives
checkOr :: Prop -> Maybe Prop
checkOr p@(p1 :||: p2) = Just p
checkOr _ = Nothing

checkAnd :: Prop -> Maybe Prop
checkAnd p@(p1 :&&: p2) = Just p
checkAnd _ = Nothing

checkNot :: Prop -> Maybe Prop
checkNot p@(Not _) = Just p
checkNot _ = Nothing

checkImpl :: Prop -> Maybe Prop
checkImpl p@(p1 :->: p2) = Just p
checkImpl _ = Nothing

checkBiImpl :: Prop -> Maybe Prop
checkBiImpl p@(p1 :<->: p2) = Just p
checkBiImpl _ = Nothing

-- Original rules remain unchanged
orR :: Rule
orR (antecedent :|=: succedent) = case findMainConnective checkOr succedent of
    Just (p :||: q, rest) -> Just [antecedent :|=: (p : q : rest)]
    _ -> Nothing

orL :: Rule
orL (antecedent :|=: succedent) = case findMainConnective checkOr antecedent of
    Just (p :||: q, rest) -> Just [rest ++ [p] :|=: succedent, rest ++ [q] :|=: succedent]
    _ -> Nothing

andR :: Rule
andR (antecedent :|=: succedent) = case findMainConnective checkAnd succedent of
    Just (p :&&: q, rest) -> Just [antecedent :|=: (p:rest), antecedent :|=: (q:rest)]
    _ -> Nothing

andL :: Rule
andL (antecedent :|=: succedent) = case findMainConnective checkAnd antecedent of
    Just (p :&&: q, rest) -> Just [rest ++ [p, q] :|=: succedent]
    _ -> Nothing

notR :: Rule
notR (antecedent :|=: succedent) = case findMainConnective checkNot succedent of
    Just (Not p, rest) -> Just [p:antecedent :|=: rest]
    _ -> Nothing

notL :: Rule
notL (antecedent :|=: succedent) = case findMainConnective checkNot antecedent of
    Just (Not p, rest) -> Just [rest :|=: p:succedent]
    _ -> Nothing

-- New rules for implication
implR :: Rule
implR (antecedent :|=: succedent) = case findMainConnective checkImpl succedent of
    Just (p :->: q, rest) -> Just [p:antecedent :|=: q:rest]
    _ -> Nothing

implL :: Rule
implL (antecedent :|=: succedent) = case findMainConnective checkImpl antecedent of
    Just (p :->: q, rest) -> Just [rest :|=: p:succedent, rest ++ [q] :|=: succedent]
    _ -> Nothing

-- New rules for bi-implication
biImplR :: Rule
biImplR (antecedent :|=: succedent) = case findMainConnective checkBiImpl succedent of
    Just (p :<->: q, rest) -> Just [antecedent :|=: (p :->: q):rest, antecedent :|=: (q :->: p):rest]
    _ -> Nothing

biImplL :: Rule
biImplL (antecedent :|=: succedent) = case findMainConnective checkBiImpl antecedent of
    Just (p :<->: q, rest) -> Just [rest ++ [p :->: q, q :->: p] :|=: succedent]
    _ -> Nothing

-- Identity Rule (I)
identity :: Rule
identity (antecedent :|=: succedent)
    | any (`elem` succedent) antecedent = Just []
    | otherwise = Nothing

-- Updated rules list with new rules
rules :: [Rule]
rules = [identity, orR, orL, andR, andL, notR, notL, implR, implL, biImplR, biImplL]

-- Main prove function
prove :: Sequent -> [Sequent]
prove sequent
    | checkIdentity sequent = []
    | otherwise = nub $ proveSearch [sequent] []

-- Helper function to check identity
checkIdentity :: Sequent -> Bool
checkIdentity (antecedent :|=: succedent) = 
    any (`elem` succedent) antecedent

-- Helper function for proof search
proveSearch :: [Sequent] -> [Sequent] -> [Sequent]
proveSearch [] proven = proven
proveSearch (s:ss) proven
    | checkIdentity s = proveSearch ss proven
    | isComplete s = s : proveSearch ss proven
    | otherwise = case tryRules s rules of
        [] -> [s]
        newSeqs -> proveSearch (newSeqs ++ ss) proven

-- Apply rules until one succeeds
tryRules :: Sequent -> [Rule] -> [Sequent]
tryRules s [] = []
tryRules s (r:rs) = case r s of
    Just seqs -> seqs
    Nothing -> tryRules s rs

-- Check if a sequent is complete (only atomic propositions)
isComplete :: Sequent -> Bool
isComplete (antecedent :|=: succedent) = 
    all isAtomic antecedent && all isAtomic succedent

-- Check if a proposition is atomic
isAtomic :: Prop -> Bool
isAtomic (Var _) = True
isAtomic _ = False

-- Optional challenge part
proveCount :: Sequent -> ([Sequent], Int)
proveCount sequent = let p = prove sequent in (p, length p)
