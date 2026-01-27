{-# OPTIONS --cubical --guardedness #-}
module Boole.EquivHelper where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Bool

module _ {ℓ ℓ' : Level} {A : CommRing ℓ} {B : CommRing ℓ'}
         (hom : CommRingHom A B)
         (inv : ⟨ B ⟩ → ⟨ A ⟩ )
         (rightInv : section (fst hom) (inv))
         (leftInv  : retract (fst hom) (inv)) where
  open CommRingStr (snd B)
  opaque 
    isoToCommRingEquiv : CommRingEquiv A B
    isoToCommRingEquiv .fst .fst = fst hom
    isoToCommRingEquiv .fst .snd .equiv-proof b .fst .fst = inv b
    isoToCommRingEquiv .fst .snd .equiv-proof b .fst .snd = rightInv b
    isoToCommRingEquiv .fst .snd .equiv-proof b .snd (a , ha=b) = Σ≡Prop (λ _ → is-set _ _) $ 
      cong inv (sym ha=b) ∙ leftInv a
    isoToCommRingEquiv .snd = snd hom 

opaque
  isoHomToCommRingEquiv : 
    {ℓ ℓ' : Level} → {A : CommRing ℓ} → {B : CommRing ℓ'} →
    (hom : CommRingHom A B) → (inv : CommRingHom B A) →
    (rightInv : hom ∘cr inv ≡ idCommRingHom B ) → (leftInv  : inv ∘cr hom ≡ idCommRingHom A ) → 
    CommRingEquiv A B
  isoHomToCommRingEquiv hom inv rightInv leftInv = isoToCommRingEquiv hom (fst inv) 
    (funExt⁻ $ cong fst rightInv) 
    (funExt⁻ $ cong fst leftInv ) 



