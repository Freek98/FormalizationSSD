{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.CountablyPresentedEquivalence where 

open import CountablyPresentedBooleanRings.PresentedBoole
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
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
open import Cubical.Algebra.BooleanRing
open import BasicDefinitions


countable-presentation→quotientFreeℕPresentation : (B : BooleanRing ℓ-zero) → has-quotient-of-freeℕ-presentation B → has-countable-presentation B
countable-presentation→quotientFreeℕPresentation B x = ℕ , countℕ , ℕ , countℕ , x

countable-presentation-equivalence : (B : BooleanRing ℓ-zero) → 
  (has-countable-presentation B) ↔ has-quotient-of-freeℕ-presentation B
countable-presentation-equivalence B = {! !} 

module omegaCore (α γ : binarySequence) where
  private
    A' = Σ[ n ∈ ℕ ] α n ≡ true
    r = gensThatAreNotInA α

  quotientOfFreeIsCP :
    (f : (Σ[ n ∈ ℕ ] γ n ≡ true) → ⟨ freeBA A' ⟩) →
    has-Boole-ω' (freeBA A' QB./Im f)
  quotientOfFreeIsCP f = subst has-Boole-ω' (sym chainPath) step5 where
    g : ℕ → ⟨ freeBA A' ⟩
    g = QC.expand.g {γ = γ} {ℓ = ℓ-zero} (freeBA A') f

    expandEquiv : BooleanRingEquiv (freeBA A' QB./Im g) (freeBA A' QB./Im f)
    expandEquiv = QC.expand.claim {γ} (freeBA A') f
  
    test : (freeBA ℕ QB./Im r) ≡ freeAcp α
    test = refl 
    fwdEquiv : BooleanRingEquiv (freeBA A') (freeBA ℕ QB./Im r)
--    fwdEquiv = invBooleanRingEquiv (freeAcp α) (freeBA A') {! freeAcpfreeAα  !} -- (freeAcp≃freeA α)
    fwdEquiv .fst .fst = fst (freeA→freeAcp α)
    fwdEquiv .fst .snd = isoToIsEquiv myIso where
      myIso : Iso ⟨ freeBA A' ⟩ ⟨ freeBA ℕ QB./Im r ⟩
      myIso .Iso.fun = fst (freeA→freeAcp α)
      myIso .Iso.inv = fst (freeAcp→freeA α)
      myIso .Iso.sec = funExt⁻ (freeAcp→freeAcp≡id α)
      myIso .Iso.ret = funExt⁻ (cong fst (freeA→freeA≡id α))
    fwdEquiv .snd = snd (freeA→freeAcp α)

    liftG : ℕ → ⟨ freeBA ℕ ⟩
    liftG = fst (freeA→freeℕ α) ∘ g

    quotEquiv : BooleanRingEquiv (freeBA A' QB./Im g)
      ((freeBA ℕ QB./Im r) QB./Im (fst (freeA→freeAcp α) ∘ g))
    quotEquiv = equivQuot.equivQuotient fwdEquiv g

    step5 : has-Boole-ω' ((freeBA ℕ QB./Im r) QB./Im (fst QB.quotientImageHom ∘ liftG))
    step5 = iteratedQuotientPresented r liftG

    chainPath : freeBA A' QB./Im f ≡
      (freeBA ℕ QB./Im r) QB./Im (fst QB.quotientImageHom ∘ liftG)
    chainPath = sym (uaBoolRing expandEquiv) ∙ uaBoolRing quotEquiv

has-Boole→has-Boole' : (B : BooleanRing ℓ-zero) → has-Boole-ω B → has-Boole-ω' B
has-Boole→has-Boole' B bω = subst has-Boole-ω' (sym (uaBoolRing eB)) quotientCP where
  A   = fst bω
  csA = fst (snd bω)
  α   = fst csA
  σA  = snd csA
  X   = fst (snd (snd bω))
  csX = fst (snd (snd (snd bω)))
  γ   = fst csX
  σX  = snd csX
  f   = fst (snd (snd (snd (snd bω))))
  eB  = snd (snd (snd (snd (snd bω))))

  A' = Σ[ n ∈ ℕ ] α n ≡ true
  X' = Σ[ n ∈ ℕ ] γ n ≡ true

  quotientCP : has-Boole-ω' (freeBA A QB./Im f)
  quotientCP =
    J (λ T _ → (f' : X → ⟨ freeBA T ⟩) → has-Boole-ω' (freeBA T QB./Im f'))
      (J (λ Y _ → (f' : Y → ⟨ freeBA A' ⟩) → has-Boole-ω' (freeBA A' QB./Im f'))
         (omegaCore.quotientOfFreeIsCP α γ)
         (sym (isoToPath σX)))
      (sym (isoToPath σA))
      f

--is-countably-presented-equivalence : 
--is-countably-presented : (B : BooleanRing ℓ-zero) → Type₁
--is-countably-presented B = ∥ has-countable-presentation B ∥₁
--
--has-quotient-of-freeℕ-presentation : (B : BooleanRing ℓ-zero) → Type₀
--has-quotient-of-freeℕ-presentation B = Σ[ f ∈ (ℕ → ⟨ freeBA ℕ ⟩) ] B is-presented-by ℕ / f
--
--is-countably-presented-alt : (B : BooleanRing ℓ-zero) → Type₀ 
--is-countably-presented-alt B = ∥ has-quotient-of-freeℕ-presentation B ∥₁
