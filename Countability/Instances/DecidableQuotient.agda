module Countability.Instances.DecidableQuotient where

open import Countability.Base
open import Countability.Instances.DecidableSubsets
open import BinarySequences.Definitions
open import BinarySequences.Properties

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import Cubical.Relation.Nullary renaming (Discrete to hasDecidableEquality)
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT
open Iso

private
  variable
    ℓ ℓ' : Level

hasBoolEquality : Type ℓ → Type ℓ
hasBoolEquality X = (x y : X) → Σ[ b ∈ Bool ] Iso (x ≡ y) (b ≡ true)

private
  Dec→BoolIso : {A : Type ℓ} → isProp A → (d : Dec A) → Iso A (Dec→Bool d ≡ true)
  Dec→BoolIso pA (yes a) =
    iso (λ _ → refl) (λ _ → a) (λ r → isSetBool true true refl r) (pA a)
  Dec→BoolIso pA (no ¬a) =
    iso (λ a → ex-falso (¬a a)) (λ r → ex-falso (false≢true r))
        (λ r → ex-falso (false≢true r)) (λ a → ex-falso (¬a a))

hasDecidableEquality→hasBoolEquality :
  {X : Type ℓ} → hasDecidableEquality X → hasBoolEquality X
hasDecidableEquality→hasBoolEquality disX x y =
  Dec→Bool (disX x y) , Dec→BoolIso (Discrete→isSet disX x y) (disX x y)

hasBoolEquality→hasDecidableEquality :
  {X : Type ℓ} → hasBoolEquality X → hasDecidableEquality X
hasBoolEquality→hasDecidableEquality h x y with h x y
... | (true  , e) = yes (inv e refl)
... | (false , e) = no λ p → false≢true (fun e p)

module DecQuotientSequence
  (α : binarySequence) (B : Type ℓ) (eqB : hasBoolEquality B)
  (q : Σℕ1 α → B) (qSurj : isSurjection q) where

  private
    A = Σℕ1 α

  module BooleanFiber (b : B) where
    isInFiber : A → Bool
    isInFiber a = fst (eqB (q a) b)

    open ΣℕSubBinarySequence α isInFiber
    open AtMostOneHit ΣαPSequence
    open ℕ∞SequenceProperties onlyFirstHit atMostOneHitInOnlyFirstHit using (isPropΣℕ1)

    isFirstInFiber : A → Bool
    isFirstInFiber a = onlyFirstHit (fst a)

    firstInFiberSubset : Type
    firstInFiberSubset = Σℕ1 onlyFirstHit

    fiberInhabited : ∥ Σℕ1 ΣαPSequence ∥₁
    fiberInhabited = PT.map
      (λ ((n , p) , qa=b) → n , ΣαPSequence-intro n p (fun (snd (eqB (q (n , p)) b)) qa=b))
      (qSurj b)

    fiberWitness : firstInFiberSubset
    fiberWitness = αToOnlyFirstHit (splitSupportΣℕ1 ΣαPSequence fiberInhabited)

    isPropFirstInFiber : isProp firstInFiberSubset
    isPropFirstInFiber = isPropΣℕ1

    isContrFirstInFiber : isContr firstInFiberSubset
    isContrFirstInFiber = fiberWitness , isPropFirstInFiber fiberWitness

    toA : firstInFiberSubset → A
    toA (n , firstHit) = n , fst (ΣαPSequence-elim n (onlyFirstHitToα n firstHit))

    isFirstInFiber→qVal : (a : A) → isFirstInFiber a ≡ true → q a ≡ b
    isFirstInFiber→qVal (n , p) fa =
      q (n , p)           ≡⟨ cong q (Σ≡Prop (λ k → isSetBool (α k) true) refl) ⟩
      q (n , fst fibElim) ≡⟨ inv (snd (eqB (q (n , fst fibElim)) b)) (snd fibElim) ⟩
      b ∎
      where
        fibElim : Σ[ q ∈ α n ≡ true ] isInFiber (n , q) ≡ true
        fibElim = ΣαPSequence-elim n (onlyFirstHitToα n fa)

  containsNewBpoint : A → Bool
  containsNewBpoint a = BooleanFiber.isFirstInFiber (q a) a

  ΣANewBPoints : Type
  ΣANewBPoints = Σ[ a ∈ A ] containsNewBpoint a ≡ true

  BTotal : Type ℓ
  BTotal = Σ[ b ∈ B ] BooleanFiber.firstInFiberSubset b

  BTotal≅B : Iso BTotal B
  BTotal≅B = equivToIso (Σ-contractSnd BooleanFiber.isContrFirstInFiber)

  BTotal≅ΣANewBPoints : Iso BTotal ΣANewBPoints
  fun BTotal≅ΣANewBPoints (b , (n , firstHit)) =
    a , subst (λ b' → BooleanFiber.isFirstInFiber b' a ≡ true)
              (sym (BooleanFiber.isFirstInFiber→qVal b a firstHit)) firstHit
    where a = BooleanFiber.toA b (n , firstHit)
  inv BTotal≅ΣANewBPoints (a , ca) = q a , (fst a , ca)
  sec BTotal≅ΣANewBPoints (a , ca) =
    Σ≡Prop (λ a' → isSetBool (containsNewBpoint a') true)
           (Σ≡Prop (λ k → isSetBool (α k) true) refl)
  ret BTotal≅ΣANewBPoints (b , (n , firstHit)) =
    Σ≡Prop BooleanFiber.isPropFirstInFiber $ isFirstInFiber→qVal (toA (n , firstHit)) firstHit where
    open BooleanFiber b

  B≅ΣANewBPoints : Iso B ΣANewBPoints
  B≅ΣANewBPoints = compIso (invIso BTotal≅B) BTotal≅ΣANewBPoints

  countabilityStructureB : has-Countability-structure B
  countabilityStructureB =
    let (γ , ΣANewBPointsIso) = countabilityStructureDecidableSubset A containsNewBpoint (α , idIso)
    in γ , compIso B≅ΣANewBPoints ΣANewBPointsIso

countabilityStructureDecidableQuotient :
  {A : Type ℓ} {B : Type ℓ'} → hasBoolEquality B → (f : A → B) → isSurjection f →
  has-Countability-structure A → has-Countability-structure B
countabilityStructureDecidableQuotient {A = A} {B = B} eqB f fSurj (α , e) =
  countabilityStructureB
  where
    eInvSurj : Σℕ1 α ↠ A
    eInvSurj = (inv e , section→isSurjection (ret e))
    qSurj : Σℕ1 α ↠ B
    qSurj = compSurjection eInvSurj (f , fSurj)
    open DecQuotientSequence α B eqB (fst qSurj) (snd qSurj)

countabilityStructureDiscreteQuotient :
  {A : Type ℓ} {B : Type ℓ'} →
  hasDecidableEquality B → (f : A ↠ B) →
  has-Countability-structure A → has-Countability-structure B
countabilityStructureDiscreteQuotient disB (f , fSurj) =
  countabilityStructureDecidableQuotient (hasDecidableEquality→hasBoolEquality disB) f fSurj

is-countable-decidable-quotient :
  {A : Type ℓ} {B : Type ℓ'} → hasBoolEquality B → (f : A ↠ B) →
  is-countable A → is-countable B
is-countable-decidable-quotient eqB (f , surjf) =
  PT.map (countabilityStructureDecidableQuotient eqB f surjf)

is-countable-discrete-quotient :
  {A : Type ℓ} {B : Type ℓ'} →
  hasDecidableEquality B → A ↠ B →
  is-countable A → is-countable B
is-countable-discrete-quotient disB =
  is-countable-decidable-quotient (hasDecidableEquality→hasBoolEquality disB)
