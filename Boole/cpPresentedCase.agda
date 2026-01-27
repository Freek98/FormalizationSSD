{-# OPTIONS --cubical --guardedness #-}
module Boole.cpPresentedCase where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

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
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Boole.PresentedBoole
open import Boole.FreeCase
open import Boole.QuotientCase
open import WLPO 

module _ ( α γ : binarySequence) where
  A = Σ[ n ∈ ℕ ] α n ≡ true
  X = Σ[ n ∈ ℕ ] γ n ≡ true
  module _ (f : X → ⟨ freeBA A ⟩ ) where

    fExtendedToAllGens : X → ⟨ freeBA ℕ ⟩ 
    fExtendedToAllGens = (fst (freeA→freeℕ α)) ∘ f
  
    prefreeA'/f' : BooleanRing ℓ-zero
    prefreeA'/f' = freeBA ℕ /Im fExtendedToAllGens

    freeA'/f' : BooleanRing ℓ-zero
    freeA'/f' = {! sum.A/f/πg  !} -- freeA' α /Im ((fst $ quotientImageHom) ∘ fExtendedToAllGens) 
    
    opaque
      unfolding sum.A/f+g
      unfolding sum.A/f/πg
      unfolding sum.conclusion
      unfolding QB._/Im_
        
--      claim : BooleanRingEquiv (freeBA ℕ /Im (⊎.rec fExtendedToAllGens (gensThatAreNotInA α)) ) freeA'/f' 
--      claim = {!  !} 
--      claim' : CommRingEquiv ((BooleanRing→CommRing (freeBA ℕ)) IQ./Im ⊎.rec ({! !}) {! !}) {! !} 
--      claim' =  sum.conclusion (BooleanRing→CommRing (freeBA ℕ)) (gensThatAreNotInA α) (expand.g {γ = γ} (freeBA ℕ) fExtendedToAllGens) 
---- sum.conclusion (BooleanRing→CommRing (freeBA ℕ))

      goal : has-Boole-ω' $ (freeBA A) /Im f
      goal = {! !} 





