
module StoneSpaces.Examples.Ninfty where

open import StoneSpaces.Spectrum
open import Cubical.Data.Unit

open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma hiding (_∧_)
open import Cubical.Relation.Nullary
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.HITs.PropositionalTruncation as PT
open import CountablyPresentedBooleanRings.Examples.Bool
open import CountablyPresentedBooleanRings.Examples.TrivialBA
open import Cubical.Algebra.BooleanRing.Initial
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BooleanRing.FreeBooleanRing.FreeBool
open import Cubical.Algebra.CommRing

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Isomorphism
open import AntiEquivalence
open import BasicDefinitions
open import Cubical.Algebra.BooleanRing
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open import CountablyPresentedBooleanRings.Examples.NFinCofin
open import BooleanRing.BooleanRingQuotients.QuotientBool
open import BooleanRing.BoolAlgMorphism

open BooleanAlgebraStr ⦃...⦄
open BooleanRingStr ⦃...⦄
instance 
  _ = snd $ freeBA ℕ
  _ = snd $ presentation

hits1AtMostOnce : binarySequence → Type 
hits1AtMostOnce α = ∀ (n m : ℕ) → α n ≡ true → α m ≡ true → n ≡ m 

isPropHits1AtMostOnce : (α : binarySequence) → isProp (hits1AtMostOnce α)
isPropHits1AtMostOnce α = isPropΠ4 λ n m _ _ → isSetℕ n m 

hits1NotTwice : binarySequence → Type 
hits1NotTwice α = ∀ (n m : ℕ) → ((m ≡ n) → ⊥) → α m and α n ≡ false

atMostOnce→NotTwice : (α : binarySequence) → hits1AtMostOnce α → hits1NotTwice α 
atMostOnce→NotTwice α atMostOnce n m n≢m = case (α m =B false , α n =B false) 
  return (λ _ → α m and α n ≡ false) of λ 
    { (yes p , yes p₁) → cong₂ _and_ p p₁
    ; (yes p , no ¬p) → cong (λ b → b and α n) p
    ; (no ¬p , yes p) → cong (_and_ (α m)) p ∙ and-zeroʳ (α m)
    ; (no ¬p , no ¬p₁) → ex-falso (n≢m (atMostOnce m n (¬false→true (α m) ¬p) (¬false→true (α n) ¬p₁))) } 

notTwice→AtMostOnce : (α : binarySequence) → hits1NotTwice α → hits1AtMostOnce α 
notTwice→AtMostOnce α notTwice m n αm=1 αn=1 = case discreteℕ m n return (λ _ → m ≡ n) of 
  λ { (yes p) → p
    ; (no ¬p) → ex-falso (true≢false $ 
      true 
        ≡⟨ sym $ cong₂ _and_ αm=1 αn=1 ⟩ 
      α m and α n 
        ≡⟨ notTwice n m ¬p ⟩ 
      false ∎ ) } 

ℕ∞ : Type ℓ-zero
ℕ∞ = Σ[ α ∈ binarySequence ] hits1AtMostOnce α

SpB∞ : Type ℓ-zero
SpB∞ = SpGeneralBooleanRing presentation

--universalPropertyPresentation : 


--SpB∞AsUniversalProperty : 

Sp→BinarySequence : SpB∞ → binarySequence
Sp→BinarySequence f n = (f ∘cr quotientImageHom) $cr generator n


open IsCommRingHom
open isBoolAlgHom

SpHits1AtMostOnce : (f : SpB∞) → hits1AtMostOnce (Sp→BinarySequence f) 
SpHits1AtMostOnce f n m αn=1 αm=1 = case discreteℕ n m return (λ _ → n ≡ m)  of
  λ { (yes p) → p
    ; (no ¬p) → ex-falso (true≢false $ 
      true and true 
        ≡⟨ cong₂ _and_ (sym αn=1) (sym αm=1) ⟩  
      (Sp→BinarySequence f n) and (Sp→BinarySequence f m)
        ≡⟨ sym $ pres∧ (freeBA ℕ) BoolBR (fst (f ∘cr quotientImageHom)) 
                (snd (f ∘cr quotientImageHom)) (generator n) (generator m) ⟩ 
      f $cr (quotientImageHom $cr (generator n ∧ generator m)) 
        ≡⟨ cong (fst f) (NFinCofinPresentation.gen-orth n m ¬p) ⟩  
      f $cr 𝟘
        ≡⟨ pres0 (snd f) ⟩  
      false ∎   ) } 

BinarySequence→SpFreeℕ : binarySequence → SpGeneralBooleanRing (freeBA ℕ) 
BinarySequence→SpFreeℕ = inducedBAHom ℕ BoolBR 

hits1AtMostOnce→respectsRelations : (α : binarySequence) → hits1AtMostOnce α → 
  (n m : ℕ) → BinarySequence→SpFreeℕ α $cr (relations (n , m)) ≡ false
hits1AtMostOnce→respectsRelations α α1atmostOnce n m with (discreteℕ n m)
... | yes p = pres0 (snd (BinarySequence→SpFreeℕ α))
... | no ¬p = inducedBAHom ℕ BoolBR α $cr (generator n ∧ generator m) 
                ≡⟨ pres∧ (freeBA ℕ) BoolBR (fst (inducedBAHom ℕ BoolBR α)) (snd (inducedBAHom ℕ BoolBR α)) (generator n) (generator m) ⟩ 
              (inducedBAHom ℕ BoolBR α $cr (generator n)) and
              (inducedBAHom ℕ BoolBR α $cr (generator m)) 
                ≡⟨ cong₂ _and_  
                  (funExt⁻ (evalBAInduce ℕ BoolBR α) n)
                  (funExt⁻ (evalBAInduce ℕ BoolBR α) m)
                 ⟩ 
              α n and α m 
                ≡⟨ atMostOnce→NotTwice α α1atmostOnce m n ¬p ⟩ 
              false ∎ 

neededIso : Iso SpB∞ ℕ∞
neededIso .Iso.fun f = Sp→BinarySequence f , SpHits1AtMostOnce f
neededIso .Iso.inv (α , α1atmostOnce) = inducedHom BoolBR (BinarySequence→SpFreeℕ α)
  λ n → hits1AtMostOnce→respectsRelations α α1atmostOnce (fst $ Iso.inv ℕ×ℕ≅ℕ n) (snd $ Iso.inv ℕ×ℕ≅ℕ n)
neededIso .Iso.sec (α , α1atmostOnce) = Σ≡Prop isPropHits1AtMostOnce
  (funExt (λ n → cong (λ h → h $cr generator n) (evalInduce BoolBR)) ∙ evalBAInduce ℕ BoolBR α)
neededIso .Iso.ret f = inducedHomUnique BoolBR _ _ f
  (inducedBAHomUnique ℕ BoolBR (Sp→BinarySequence f) (f ∘cr quotientImageHom) refl)

