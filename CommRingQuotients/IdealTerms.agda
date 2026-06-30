{- I'm making this into a PR for the cubical library TODO if that's merged fix the references in other files -}
module CommRingQuotients.IdealTerms where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Quotient.ImageQuotient
open import Cubical.HITs.PropositionalTruncation as PT

module _ {ℓ : Level} (R : CommRing ℓ) {X : Type ℓ} (f : X → ⟨ R ⟩)  where
  open CommRingStr ⦃...⦄
  instance
   _ = (snd R)
  data isInIdeal : (r : ⟨ R ⟩) → Type ℓ where
        isImage  : (r : ⟨ R ⟩) → (x : X) → (f x ≡ r) → isInIdeal r
        iszero   : (r : ⟨ R ⟩) → (0r ≡ r) → isInIdeal r
        isSum    : (r : ⟨ R ⟩) → (s t : ⟨ R ⟩) → (r ≡ s + t) → isInIdeal s → isInIdeal t → isInIdeal r
        isMul    : (r : ⟨ R ⟩) → (s t : ⟨ R ⟩) → (r ≡ s · t) →               isInIdeal t → isInIdeal r

  idealDecomp : ( r : ⟨ R ⟩ ) → generatedIdeal R f r → ∥ isInIdeal r ∥₁
  idealDecomp .(f x)   (single x)                    = ∣ isImage (f x) x refl ∣₁
  idealDecomp .(0r)     zero                         = ∣ iszero 0r refl ∣₁
  idealDecomp .(s + t) (add {x = s} {y = t} s∈I t∈I) = PT.map2 (isSum (s + t) s t refl) (idealDecomp s s∈I) (idealDecomp t t∈I)
  idealDecomp .(s · t) (mul {r = s} {x = t} t∈I )    = PT.map  (isMul (s · t) s t refl) (idealDecomp t t∈I)
  idealDecomp r        (squash r∈I r∈I' i)           = ∥∥-isPropDep isInIdeal
                                                       (idealDecomp r r∈I) (idealDecomp r r∈I') refl i
  
  private 
    substInIdeal : {r s : ⟨ R ⟩} → s ≡ r → generatedIdeal R f s → generatedIdeal R f r
    substInIdeal = subst (generatedIdeal R f)

  addSquash : (r : ⟨ R ⟩) → isInIdeal r → generatedIdeal R f r
  addSquash r (isImage .r x fx=r) = substInIdeal fx=r (single x)
  addSquash r (iszero .r 0=r) = substInIdeal 0=r zero
  addSquash r (isSum .r s t r=s+t s∈I t∈I) = substInIdeal (sym r=s+t) (add (addSquash s s∈I) (addSquash t t∈I))
  addSquash r (isMul .r s t r=s·t t∈I) = substInIdeal (sym r=s·t) (mul (addSquash t t∈I))

