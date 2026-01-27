{-# OPTIONS --cubical --guardedness #-}

module Boole.freeBAN where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
{- I got a unification problem for using rec* in EmptyQuotient, 
-- which is needed as that's what the image quotient uses, which maybe was a design mistake
-}
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import FreeBool
import FreeBool as FB

open import SurjectiveTerms
open import freeBATerms

open import QuotientBool as QB
--open import NaturalNumbersProperties.NBijection
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import WLPO
open import CommRingQuotients.EmptyQuotient
open import Boole.PresentedBoole

opaque
  unfolding _/Im_

  emptyquot : BooleanRingEquiv (freeBA ℕ) (freeBA ℕ /Im empty-func)
  emptyquot = commRingEquiv→BooleanRingEquiv $ emptyQuotientEquiv (BooleanRing→CommRing (freeBA ℕ))

