{-# OPTIONS --lossy-unification #-}
-- comes from an LLM discussion
module CountablyPresentedBooleanRings.QuotientClosureFromCountableChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import Cubical.Data.Bool
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Isomorphism
open import Axioms.DependentChoice

open import BasicDefinitions
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.BoolRingUnivalence
open import BooleanRing.BooleanRingMaps
open import BooleanRing.BooleanRingQuotients.QuotientBool
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions as CPE

module _ (cc : CountableChoice {ℓ-zero} {ℓ-zero})
         (C : BooleanRing ℓ-zero) (C-pres : is-countably-presented C)
         (R : Type) (Rcount : has-Countability-structure R)
         (f : R → ⟨ C ⟩) where

  -- Everything below is parametrised by a concrete presentation `C ≅ freeBA ℕ /Im rC`; it is
  -- supplied (and the propositional truncation discharged) in `quotient-by-countable-preserves-cp`.
  module fromPresentation (rC : ℕ → ⟨ freeBA ℕ ⟩) (eC : C is-presented-by ℕ / rC) where
    D : BooleanRing ℓ-zero
    D = freeBA ℕ /Im rC

    π : BoolHom (freeBA ℕ) D
    π = quotientImageHom {B = freeBA ℕ} {f = rC}

    relUp : R → ⟨ D ⟩
    relUp = fst (fst eC) ∘ f

    C/f≅ : BoolRingEquiv (C /Im f) (D /Im relUp)
    C/f≅ = EquivQuotBR eC f

    LiftData : Type
    LiftData = Σ[ f↑ ∈ (R → ⟨ freeBA ℕ ⟩) ]
                 ((r : R) → π $cr (f↑ r) ≡ relUp r)

    presFromLift : LiftData → has-quotient-of-freeℕ-presentation (C /Im f)
    presFromLift (f↑ , lifts) =
      subst has-quotient-of-freeℕ-presentation (sym bigPath)
            (CPE.quotient-of-sum-presentation.doubleQuotientPresented rC f↑Exp)
      where
        open IsCommRingHom (snd π) using (pres0)
        γR = fst Rcount
        eR = snd Rcount
        f↑X : Σℕ γR → ⟨ freeBA ℕ ⟩
        f↑X = f↑ ∘ Iso.inv eR
        relUpX : Σℕ γR → ⟨ D ⟩
        relUpX = relUp ∘ Iso.inv eR
        f↑Exp : ℕ → ⟨ freeBA ℕ ⟩
        f↑Exp = CPE.quotientByCountable.g γR (freeBA ℕ) f↑X

        commute : (n : ℕ) → CPE.quotientByCountable.g γR D relUpX n ≡ π $cr (f↑Exp n)
        commute n = case γR n ≟ true return (λ d →
              g' D relUpX n d
            ≡ π $cr (g' (freeBA ℕ) f↑X n d))
          of λ {
            (yes p) → sym (lifts (Iso.inv eR (n , p))) ;
            (no ¬p) → sym pres0} where
              open CPE.quotientByCountable γR

        bigEquiv : BooleanRingEquiv (C /Im f) (D /Im (CPE.quotientByCountable.g γR D relUpX))
        bigEquiv = invBooleanRingEquiv _ _ (CPE.quotientByCountable.quotient-by-expansion-equiv γR D relUpX)
                 ∘cre reindexwithEquiv eR relUp
                 ∘cre C/f≅

        bigPath : (C /Im f) ≡ (D /Im (fst π ∘ f↑Exp))
        bigPath = uaBoolRing bigEquiv ∙ cong (λ h → D /Im h) (funExt commute)

    lift-f : ∥ LiftData ∥₁
    lift-f = PT.map (Iso.fun Σ-Π-Iso)
               (cc R Rcount
                 (λ r → Σ[ t ∈ ⟨ freeBA ℕ ⟩ ] (π $cr t ≡ relUp r))
                 (λ r → quotientImageHomSurjective {B = freeBA ℕ} {f = rC} (relUp r)))


    cp-alt : is-countably-presented-alt (C /Im f)
    cp-alt = PT.map presFromLift lift-f

  quotient-by-countable-preserves-cp : is-countably-presented (C /Im f)
  quotient-by-countable-preserves-cp =
    countably-presented-equivalence (C /Im f) .snd
      (PT.rec squash₁
        (λ { (rC , eC) → fromPresentation.cp-alt rC eC })
        (countably-presented-equivalence C .fst C-pres))
