{-# OPTIONS  --lossy-unification #-}
module CountablyPresentedBooleanRings.Examples.freeN where
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.AlgebraicFacts
open import BooleanRing.BoolAlgMorphism
open import Cubical.Foundations.Equiv
open import Cubical.Tactics.NatSolver
open import Cubical.Tactics.CommRingSolver
open import BooleanRing.BooleanRingMaps
open import BooleanRing.SubBooleanRing
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_) 
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Bool

open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Bool renaming ( _≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Algebra.CommRing.Instances.Unit
open import QuickFixes

open BooleanAlgebraStr ⦃...⦄
open BooleanRingStr ⦃...⦄

freeℕ : BooleanRing ℓ-zero
ℙℕ = binarySequence , booleanStructureOnBinarySequences


