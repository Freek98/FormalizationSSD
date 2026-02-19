{-# OPTIONS --cubical --guardedness #-}
module BooleanRing.BooleanRingQuotients.QuotientEquivalences where 

open import QuotientBool as QB
open import BasicDefinitions
open import CommRingQuotients.EquivHelper 
open import CountablyPresentedBooleanRings.PresentedBoole 
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import BooleanRing.FreeBooleanRing.FreeBool

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat 
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Relation.Nullary

-- Reindexing: if σ : Iso X Y, then A /Im f ≅ A /Im (f ∘ Iso.inv σ)
module reindex {A : BooleanRing ℓ-zero} {X Y : Type} (σ : Iso X Y) (f : X → ⟨ A ⟩) where
  open BooleanRingStr ⦃...⦄
  instance
    _ = snd A
    _ = snd (A QB./Im f)
    _ = snd (A QB./Im (f ∘ Iso.inv σ))

  f' : Y → ⟨ A ⟩
  f' = f ∘ Iso.inv σ

  fwdKills : (x : X) → QB.quotientImageHom {B = A} {f = f'} $cr f x ≡ 𝟘
  fwdKills x = subst (λ a → QB.quotientImageHom {B = A} {f = f'} $cr a ≡ 𝟘)
    (cong f (Iso.ret σ x))
    (QB.zeroOnImage (Iso.fun σ x))

  fwd : BoolHom (A QB./Im f) (A QB./Im f')
  fwd = QB.inducedHom (A QB./Im f') QB.quotientImageHom fwdKills

  bwdKills : (y : Y) → QB.quotientImageHom {B = A} {f = f} $cr f' y ≡ 𝟘
  bwdKills y = QB.zeroOnImage (Iso.inv σ y)

  bwd : BoolHom (A QB./Im f') (A QB./Im f)
  bwd = QB.inducedHom (A QB./Im f) QB.quotientImageHom bwdKills

  fwd∘π : fwd ∘cr QB.quotientImageHom {B = A} {f = f} ≡ QB.quotientImageHom
  fwd∘π = QB.evalInduce (A QB./Im f')

  bwd∘π : bwd ∘cr QB.quotientImageHom {B = A} {f = f'} ≡ QB.quotientImageHom
  bwd∘π = QB.evalInduce (A QB./Im f)

  ret∘π : (bwd ∘cr fwd) ∘cr QB.quotientImageHom {B = A} {f = f} ≡
          idCommRingHom (BooleanRing→CommRing (A QB./Im f)) ∘cr QB.quotientImageHom
  ret∘π =
    (bwd ∘cr fwd) ∘cr QB.quotientImageHom
      ≡⟨ CommRingHom≡ refl ⟩
    bwd ∘cr (fwd ∘cr QB.quotientImageHom)
      ≡⟨ cong (bwd ∘cr_) fwd∘π ⟩
    bwd ∘cr QB.quotientImageHom {B = A} {f = f'}
      ≡⟨ bwd∘π ⟩
    QB.quotientImageHom
      ≡⟨ sym (idCompCommRingHom QB.quotientImageHom) ⟩
    idCommRingHom _ ∘cr QB.quotientImageHom ∎

  sec∘π : (fwd ∘cr bwd) ∘cr QB.quotientImageHom {B = A} {f = f'} ≡
          idCommRingHom (BooleanRing→CommRing (A QB./Im f')) ∘cr QB.quotientImageHom
  sec∘π =
    (fwd ∘cr bwd) ∘cr QB.quotientImageHom
      ≡⟨ CommRingHom≡ refl ⟩
    fwd ∘cr (bwd ∘cr QB.quotientImageHom)
      ≡⟨ cong (fwd ∘cr_) bwd∘π ⟩
    fwd ∘cr QB.quotientImageHom {B = A} {f = f}
      ≡⟨ fwd∘π ⟩
    QB.quotientImageHom
      ≡⟨ sym (idCompCommRingHom QB.quotientImageHom) ⟩
    idCommRingHom _ ∘cr QB.quotientImageHom ∎

  ret : bwd ∘cr fwd ≡ idCommRingHom (BooleanRing→CommRing (A QB./Im f))
  ret = CommRingHom≡ $
    QB.quotientImageHomEpi {B = A} {f = f}
      (⟨ A QB./Im f ⟩ , BooleanRingStr.is-set (snd (A QB./Im f)))
      (cong fst ret∘π)

  sec : fwd ∘cr bwd ≡ idCommRingHom (BooleanRing→CommRing (A QB./Im f'))
  sec = CommRingHom≡ $
    QB.quotientImageHomEpi {B = A} {f = f'}
      (⟨ A QB./Im f' ⟩ , BooleanRingStr.is-set (snd (A QB./Im f')))
      (cong fst sec∘π)

  reindexEquiv : BooleanRingEquiv (A QB./Im f) (A QB./Im f')
  reindexEquiv = isoToCommRingEquiv fwd (fst bwd)
    (funExt⁻ (cong fst sec)) (funExt⁻ (cong fst ret))

-- Quotient compatible with equivalence: if A ≅ B then A /Im h ≅ B /Im (e ∘ h)
module equivQuot {A B : BooleanRing ℓ-zero} (e : BooleanRingEquiv A B)
  {X : Type} (h : X → ⟨ A ⟩) where
  open BooleanRingStr ⦃...⦄
  instance
    _ = snd A
    _ = snd B
    _ = snd (A QB./Im h)
    _ = snd (B QB./Im (fst (fst e) ∘ h))

  eFwd : ⟨ A ⟩ → ⟨ B ⟩
  eFwd = fst (fst e)

  eBwd : ⟨ B ⟩ → ⟨ A ⟩
  eBwd = fst (fst (invBooleanRingEquiv A B e))

  eFwdHom : BoolHom A B
  eFwdHom = BooleanEquivToHom A B e

  eBwdHom : BoolHom B A
  eBwdHom = BooleanEquivToHomInv A B e

  eBwd∘eFwd : eBwdHom ∘cr eFwdHom ≡ idBoolHom A
  eBwd∘eFwd = BooleanEquivLeftInv A B e

  eFwd∘eBwd : eFwdHom ∘cr eBwdHom ≡ idBoolHom B
  eFwd∘eBwd = BooleanEquivRightInv A B e

  -- Forward: A → B /Im (e ∘ h) via e then quotient
  φ : BoolHom A (B QB./Im (eFwd ∘ h))
  φ = QB.quotientImageHom ∘cr eFwdHom

  φKills : (x : X) → φ $cr h x ≡ 𝟘
  φKills x = QB.zeroOnImage x

  fwdQ : BoolHom (A QB./Im h) (B QB./Im (eFwd ∘ h))
  fwdQ = QB.inducedHom (B QB./Im (eFwd ∘ h)) φ φKills

  -- Backward: B → A /Im h via e⁻¹ then quotient
  ψ : BoolHom B (A QB./Im h)
  ψ = QB.quotientImageHom ∘cr eBwdHom

  ψKills : (x : X) → ψ $cr (eFwd (h x)) ≡ 𝟘
  ψKills x = cong (fst QB.quotientImageHom) (funExt⁻ (cong fst eBwd∘eFwd) (h x))
    ∙ QB.zeroOnImage x

  bwdQ : BoolHom (B QB./Im (eFwd ∘ h)) (A QB./Im h)
  bwdQ = QB.inducedHom (A QB./Im h) ψ ψKills

  fwdQ∘π : fwdQ ∘cr QB.quotientImageHom {B = A} {f = h} ≡ φ
  fwdQ∘π = QB.evalInduce (B QB./Im (eFwd ∘ h))

  bwdQ∘π : bwdQ ∘cr QB.quotientImageHom {B = B} {f = eFwd ∘ h} ≡ ψ
  bwdQ∘π = QB.evalInduce (A QB./Im h)

  ret∘π : (bwdQ ∘cr fwdQ) ∘cr QB.quotientImageHom {B = A} {f = h} ≡
    idCommRingHom (BooleanRing→CommRing (A QB./Im h)) ∘cr QB.quotientImageHom
  ret∘π =
    (bwdQ ∘cr fwdQ) ∘cr QB.quotientImageHom
      ≡⟨ CommRingHom≡ refl ⟩
    bwdQ ∘cr (fwdQ ∘cr QB.quotientImageHom)
      ≡⟨ cong (bwdQ ∘cr_) fwdQ∘π ⟩
    bwdQ ∘cr (QB.quotientImageHom ∘cr eFwdHom)
      ≡⟨ CommRingHom≡ refl ⟩
    (bwdQ ∘cr QB.quotientImageHom) ∘cr eFwdHom
      ≡⟨ cong (_∘cr eFwdHom) bwdQ∘π ⟩
    (QB.quotientImageHom ∘cr eBwdHom) ∘cr eFwdHom
      ≡⟨ CommRingHom≡ refl ⟩
    QB.quotientImageHom ∘cr (eBwdHom ∘cr eFwdHom)
      ≡⟨ cong (QB.quotientImageHom ∘cr_) eBwd∘eFwd ⟩
    QB.quotientImageHom ∘cr idBoolHom A
      ≡⟨ CommRingHom≡ refl ⟩
    QB.quotientImageHom
      ≡⟨ sym (idCompCommRingHom QB.quotientImageHom) ⟩
    idCommRingHom _ ∘cr QB.quotientImageHom ∎

  sec∘π : (fwdQ ∘cr bwdQ) ∘cr QB.quotientImageHom {B = B} {f = eFwd ∘ h} ≡
    idCommRingHom (BooleanRing→CommRing (B QB./Im (eFwd ∘ h))) ∘cr QB.quotientImageHom
  sec∘π =
    (fwdQ ∘cr bwdQ) ∘cr QB.quotientImageHom
      ≡⟨ CommRingHom≡ refl ⟩
    fwdQ ∘cr (bwdQ ∘cr QB.quotientImageHom)
      ≡⟨ cong (fwdQ ∘cr_) bwdQ∘π ⟩
    fwdQ ∘cr (QB.quotientImageHom ∘cr eBwdHom)
      ≡⟨ CommRingHom≡ refl ⟩
    (fwdQ ∘cr QB.quotientImageHom) ∘cr eBwdHom
      ≡⟨ cong (_∘cr eBwdHom) fwdQ∘π ⟩
    (QB.quotientImageHom ∘cr eFwdHom) ∘cr eBwdHom
      ≡⟨ CommRingHom≡ refl ⟩
    QB.quotientImageHom ∘cr (eFwdHom ∘cr eBwdHom)
      ≡⟨ cong (QB.quotientImageHom ∘cr_) eFwd∘eBwd ⟩
    QB.quotientImageHom ∘cr idBoolHom B
      ≡⟨ CommRingHom≡ refl ⟩
    QB.quotientImageHom
      ≡⟨ sym (idCompCommRingHom QB.quotientImageHom) ⟩
    idCommRingHom _ ∘cr QB.quotientImageHom ∎

  retQ : bwdQ ∘cr fwdQ ≡ idCommRingHom (BooleanRing→CommRing (A QB./Im h))
  retQ = CommRingHom≡ $
    QB.quotientImageHomEpi {B = A} {f = h}
      (⟨ A QB./Im h ⟩ , BooleanRingStr.is-set (snd (A QB./Im h)))
      (cong fst ret∘π)

  secQ : fwdQ ∘cr bwdQ ≡ idCommRingHom (BooleanRing→CommRing (B QB./Im (eFwd ∘ h)))
  secQ = CommRingHom≡ $
    QB.quotientImageHomEpi {B = B} {f = eFwd ∘ h}
      (⟨ B QB./Im (eFwd ∘ h) ⟩ , BooleanRingStr.is-set (snd (B QB./Im (eFwd ∘ h))))
      (cong fst sec∘π)

  equivQuotient : BooleanRingEquiv (A QB./Im h) (B QB./Im (eFwd ∘ h))
  equivQuotient = isoToCommRingEquiv fwdQ (fst bwdQ)
    (funExt⁻ (cong fst secQ)) (funExt⁻ (cong fst retQ))
