{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.Point where 

open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Foundations.Equiv
open import BooleanRing.BooleanRingMaps
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Base

open import Cubical.Data.Sigma
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing.Instances.Unit

module Point where
  trivialBooleanRing : BooleanRing ℓ-zero 
  trivialBooleanRing = idemCommRing→BR UnitCommRing λ tt → refl 

  module Characterization {ℓ' : Level} (B : BooleanRing ℓ') where
        -- TODO note that you can do this for commutative rings, not just Boolean rings
    open BooleanRingStr (snd B) 
    mapToTrivialBooleanRing : BoolHom B trivialBooleanRing
    mapToTrivialBooleanRing = mapToUnitCommRing $ BooleanRing→CommRing B
    open IsCommRingHom (snd mapToTrivialBooleanRing)

    isTrivial : Type ℓ'
    isTrivial = 𝟘 ≡ 𝟙
    
    module _ (isTriv : isTrivial) where
      isTrivial→isContr : isContr ⟨ B ⟩
      isTrivial→isContr .fst = 𝟘
      isTrivial→isContr .snd b = 𝟘  ≡⟨ sym ∧AnnihilR ⟩ (b · 𝟘) ≡⟨ cong (λ c → b · c) isTriv ⟩ b · 𝟙 ≡⟨ ∧IdR ⟩  b ∎  where 
        open BooleanAlgebraStr B
  
      isTrivial→isEquivmapToTrivial : isEquiv (fst mapToTrivialBooleanRing)
      isTrivial→isEquivmapToTrivial .equiv-proof tt* = (𝟘 , pres0) , λ (b , fb=tt) → Σ≡Prop 
        (λ _ → BooleanRingStr.is-set (snd trivialBooleanRing) _ _) 
        (isTrivial→isContr .snd b ) 
    
      trivialCharacterizes : BooleanRingEquiv B trivialBooleanRing
      trivialCharacterizes .fst .fst = fst mapToTrivialBooleanRing
      trivialCharacterizes .fst .snd = isTrivial→isEquivmapToTrivial
      trivialCharacterizes .snd = snd mapToTrivialBooleanRing




