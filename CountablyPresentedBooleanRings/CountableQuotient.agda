{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.CountableQuotient where 
open import BooleanRing.BooleanRingQuotients.QuotientEquivalences

open import QuotientBool as QB
open import BasicDefinitions
open import CommRingQuotients.EquivHelper 
open import CountablyPresentedBooleanRings.PresentedBoole 
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.BoolRingUnivalence

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


module expand {γ : binarySequence} {ℓ : Level} (A : BooleanRing ℓ-zero) where
  X = Σ[ n ∈ ℕ ] γ n ≡ true 
  module _ (f : X → ⟨ A ⟩) where 
    open BooleanRingStr ⦃...⦄ 
    instance
      _ = snd A 
    g' : (n : ℕ) → (γn : Dec (γ n ≡ true)) → ⟨ A ⟩
    g' n (yes p) = f (n , p)
    g' n (no ¬p) = 𝟘
    g : ℕ → ⟨ A ⟩
    g n  = g' n (γ n =B true) 
    gYesCase' : (n : ℕ) → (γn : Dec (γ n ≡ true)) → (p : γ n ≡ true) → g' n γn ≡ f ( n , p)
    gYesCase' n (yes _) _ = cong f (Σ≡Prop (λ x → isSetBool _ _) refl)
    gYesCase' n (no ¬p) p = ex-falso $ ¬p p 
    gYesCase : (n : ℕ) → ( p : γ n ≡ true) → g n ≡ f (n , p)
    gYesCase n = gYesCase' n (γ n =B true)
    A/f = A QB./Im f 
    A/g = A QB./Im g
    instance 
      _ = snd A/f
      _ = snd A/g
    open IsCommRingHom (snd $ QB.quotientImageHom {B = A} {f = f} )
    fZeroOnG' : (n : ℕ) → (γn : Dec (γ n ≡ true) ) → QB.quotientImageHom {f = f} $cr g' n γn ≡ 𝟘 
    fZeroOnG' n (yes p) = QB.zeroOnImage (n , p)
    fZeroOnG' n (no ¬p) = pres0 
    fZeroOnG : (n : ℕ) → QB.quotientImageHom {f = f} $cr g n ≡ 𝟘 
    fZeroOnG n = fZeroOnG' n (γ n =B true) 
    A/g→A/f : BoolHom A/g A/f
    A/g→A/f = QB.inducedHom A/f QB.quotientImageHom fZeroOnG
    
    gZeroOnF : (x : X) → QB.quotientImageHom {f = g} $cr f x ≡ 𝟘 
    gZeroOnF x@(n , p) = cong (fst QB.quotientImageHom) (sym $ gYesCase n p) ∙ QB.zeroOnImage n 
    A/f→A/g : BoolHom A/f A/g
    A/f→A/g = QB.inducedHom A/g QB.quotientImageHom gZeroOnF 
    
    A/f→A/g∘qf=qg : A/f→A/g ∘cr (QB.quotientImageHom {f = f}) ≡ QB.quotientImageHom {f = g} 
    A/f→A/g∘qf=qg = QB.evalInduce A/g 

    A/g→A/f∘qg=qf : A/g→A/f ∘cr (QB.quotientImageHom {f = g}) ≡ QB.quotientImageHom {f = f} 
    A/g→A/f∘qg=qf = QB.evalInduce A/f  

    A/g∘q=q : A/f→A/g ∘cr A/g→A/f ∘cr QB.quotientImageHom {f = g} ≡ QB.quotientImageHom {f = g} 
    A/g∘q=q = cong (λ h → A/f→A/g ∘cr h) A/g→A/f∘qg=qf ∙ A/f→A/g∘qf=qg
    A/g=id : A/f→A/g ∘cr A/g→A/f ≡ idCommRingHom (BooleanRing→CommRing A/g)
    A/g=id = CommRingHom≡ $ 
       QB.quotientImageHomEpi (_ , is-set) (cong fst A/g∘q=q) 

    A/f∘q=q : A/g→A/f ∘cr A/f→A/g ∘cr QB.quotientImageHom {f = f} ≡ QB.quotientImageHom {f = f} 
    A/f∘q=q = cong (λ h → A/g→A/f ∘cr h) A/f→A/g∘qf=qg ∙ A/g→A/f∘qg=qf
    A/f=id : A/g→A/f ∘cr A/f→A/g ≡ idCommRingHom (BooleanRing→CommRing A/f)
    A/f=id =  CommRingHom≡ $ 
       QB.quotientImageHomEpi (⟨ A/f ⟩ , is-set) (cong fst A/f∘q=q)

    claim : BooleanRingEquiv A/g A/f
    claim = isoToCommRingEquiv A/g→A/f (fst A/f→A/g) (funExt⁻ $ cong fst A/f=id) (funExt⁻ $ cong fst A/g=id) 


-- Given f, g : ℕ → ⟨ freeBA ℕ ⟩, the combined quotient is countably presented.
-- freeBA ℕ /Im (⊎.rec f g) ≅ freeBA ℕ /Im k where k : ℕ → ⟨ freeBA ℕ ⟩
sumQuotientPresented : (f g : ℕ → ⟨ freeBA ℕ ⟩) → has-Boole-ω' (freeBA ℕ QB./Im (⊎.rec f g))
sumQuotientPresented f g = k , equivChain where
  k : ℕ → ⟨ freeBA ℕ ⟩
  k = ⊎.rec f g ∘ Iso.inv ℕ⊎ℕ≅ℕ

  equivChain : BooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f g)) (freeBA ℕ QB./Im k)
  equivChain = reindex.reindexEquiv ℕ⊎ℕ≅ℕ (⊎.rec f g)

-- The iterated quotient (freeBA ℕ /Im f) /Im (π ∘ g) is countably presented.
iteratedQuotientPresented : (f g : ℕ → ⟨ freeBA ℕ ⟩) →
  has-Boole-ω' ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
iteratedQuotientPresented f g = subst has-Boole-ω' (quotientEquivBool (freeBA ℕ) f g) (sumQuotientPresented f g)

module mainTheorem (B : BooleanRing ℓ-zero)
  (pres : has-Boole-ω' B) (h : ℕ → ⟨ B ⟩)
  (g : ℕ → ⟨ freeBA ℕ ⟩)
  (liftCond : fst QB.quotientImageHom ∘ g ≡ fst (fst (snd pres)) ∘ h) where

  f : ℕ → ⟨ freeBA ℕ ⟩
  f = fst pres

  e : BooleanRingEquiv B (freeBA ℕ QB./Im f)
  e = snd pres

  eFwd : ⟨ B ⟩ → ⟨ freeBA ℕ QB./Im f ⟩
  eFwd = fst (fst e)

  -- Step 1: B /Im h ≅ (freeBA ℕ /Im f) /Im (e ∘ h) via equivQuot
  step1 : BooleanRingEquiv (B QB./Im h) ((freeBA ℕ QB./Im f) QB./Im (eFwd ∘ h))
  step1 = equivQuot.equivQuotient e h

  -- Step 2: (freeBA ℕ /Im f) /Im (e ∘ h) = (freeBA ℕ /Im f) /Im (π ∘ g)
  -- by the lift condition: π ∘ g = e ∘ h
  step2Path : (freeBA ℕ QB./Im f) QB./Im (eFwd ∘ h) ≡
    (freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)
  step2Path = cong (λ q → (freeBA ℕ QB./Im f) QB./Im q) (sym liftCond)

  -- Step 3: (freeBA ℕ /Im f) /Im (π ∘ g) is countably presented
  step3 : has-Boole-ω' ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
  step3 = iteratedQuotientPresented f g

  -- Combine: B /Im h is countably presented
  result : has-Boole-ω' (B QB./Im h)
  result = subst has-Boole-ω' (sym chainPath) step3 where
    path1 : B QB./Im h ≡ (freeBA ℕ QB./Im f) QB./Im (eFwd ∘ h)
    path1 = uaBoolRing step1

    chainPath : B QB./Im h ≡ (freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)
    chainPath = path1 ∙ step2Path

-- Top-level theorem: countably presented quotients are countably presented,
-- given a lift of h through the quotient map.
countablyPresentedQuotient :
  (B : BooleanRing ℓ-zero) →
  (pres : has-Boole-ω' B) →
  (h : ℕ → ⟨ B ⟩) →
  (g : ℕ → ⟨ freeBA ℕ ⟩) →
  (liftCond : fst QB.quotientImageHom ∘ g ≡ fst (fst (snd pres)) ∘ h) →
  has-Boole-ω' (B QB./Im h)
countablyPresentedQuotient B pres h g lc = mainTheorem.result B pres h g lc
