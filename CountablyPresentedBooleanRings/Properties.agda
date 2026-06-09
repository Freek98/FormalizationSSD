module CountablyPresentedBooleanRings.Properties where
open import CountablyPresentedBooleanRings.Definitions

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.HLevels 
import Cubical.Data.Empty as ⊥

open import Cubical.Data.Bool 
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing 
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool 
open import Cubical.Algebra.BooleanRing.Initial 
open import BooleanRing.BooleanRingMaps 

open import BasicDefinitions 
open import BooleanRing.FreeBooleanRing.FreeBool 
open import StoneSpaces.Spectrum
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import Cubical.Foundations.Isomorphism
open import BooleanRing.BooleanRingQuotients.QuotientBool 
open import Countability.Properties 
open import BooleanRing.FreeBooleanRing.freeBATerms

module _ 
  {G : Type} {R : Type}
  (rel : R → ⟨ freeBA G ⟩) where
  private  
    free = freeBA G 
    B = free /Im rel 
  
    π : BoolHom free B
    π = quotientImageHom 

  agreeOnGens≡ : {ℓ : Level} (C : BooleanRing ℓ) {α β : BoolHom B C} → ((g : G) → (α ∘cr π) $cr generator g ≡ (β ∘cr π) $cr generator g) → α ≡ β
  agreeOnGens≡ C {α = α} {β = β} agree =
    CommRingHom≡ (quotientImageHomEpi {f = rel} (⟨ C ⟩ , is-set) (cong fst απ≡βπ))
    where
      open BooleanRingStr (snd C)
      απ≡βπ : α ∘cr π ≡ β ∘cr π
      απ≡βπ = equalityFromEqualityOnGenerators C (α ∘cr π) (β ∘cr π) agree


