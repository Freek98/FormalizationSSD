module OmnisciencePrinciples.WLPO where 

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import BasicDefinitions

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool

open import BooleanRing.FreeBooleanRing.SurjectiveTerms
open import BooleanRing.FreeBooleanRing.freeBATerms
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base as TV
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary.Base
open import Axioms.StoneDuality
open import StoneSpaces.Examples.Cantor
open import StoneSpaces.Spectrum

zeroSequence : binarySequence 
zeroSequence _ = false

WLPO : Type 
WLPO = ∀ (α : binarySequence) → (∀ (n : ℕ) → α n ≡ false) ⊎ (¬ (∀ (n : ℕ) → α n ≡ false))

evaluate : {A : Type} → (A → Bool) → BoolHom (freeBA A) BoolBR
evaluate {A} = inducedBAHom A BoolBR 

_$freeℕ_ : binarySequence → freeBATerms ℕ → Bool
_$freeℕ_ α a = evaluate α $cr fst includeBATermsSurj a 

>maxUsedIndex : (a : freeBATerms ℕ) → ℕ 
>maxUsedIndex (Tvar n)   = suc n
>maxUsedIndex (Tconst x) = 0
>maxUsedIndex (a +T b)   = max (>maxUsedIndex a) (>maxUsedIndex b)
>maxUsedIndex (-T a)     = >maxUsedIndex a
>maxUsedIndex (a ·T b)   = max (>maxUsedIndex a) (>maxUsedIndex b) 

δ : ℕ → binarySequence 
δ zero zero       = true
δ (suc n) zero    = false
δ zero (suc m)    = false
δ (suc n) (suc m) = δ n m 

δSnn=false : (n : ℕ ) → δ (suc n ) n ≡ false
δSnn=false zero    = refl
δSnn=false (suc n) = δSnn=false n 

δnn=true : (n : ℕ) → δ n n ≡ true
δnn=true zero    = refl
δnn=true (suc n) = δnn=true n 

miss : (a : freeBATerms ℕ) → binarySequence
miss = δ ∘ >maxUsedIndex 

_ignores_ : binarySequence → freeBATerms ℕ → Type _
α ignores a = α $freeℕ a ≡ zeroSequence $freeℕ a

opaque
  unfolding TV.var
  unfolding equalityFromEqualityOnGenerators 
  unfolding inducedBAHom
  ignoreAtoms : (n m : ℕ) → (m < n) → δ n ignores (Tvar m)
  ignoreAtoms zero _          x = ex-falso (¬-<-zero x)
  ignoreAtoms (suc n) zero    _ = refl 
  ignoreAtoms (suc n) (suc m) x = ignoreAtoms n m (predℕ-≤-predℕ x) 

  ignoreSmallTerms : (n : ℕ) → (a : freeBATerms ℕ) → (>maxUsedIndex a ≤ n) → δ n $freeℕ a ≡ zeroSequence $freeℕ a
  ignoreSmallTerms n (Tvar m)   p = ignoreAtoms n m p
  ignoreSmallTerms _ (Tconst x) _ = refl
  ignoreSmallTerms n (a +T b)   p = cong₂ _⊕_
      (ignoreSmallTerms n a (>maxUsedIndex a ≤⟨ left-≤-max  ⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎)) 
      (ignoreSmallTerms n b (>maxUsedIndex b ≤⟨ right-≤-max {>maxUsedIndex b} {>maxUsedIndex a}⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎))
  ignoreSmallTerms n (-T a)     p = ignoreSmallTerms n a p
  ignoreSmallTerms n (a ·T b)   p = cong₂ _and_
      (ignoreSmallTerms n a (>maxUsedIndex a ≤⟨ left-≤-max {>maxUsedIndex a} {>maxUsedIndex b}⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎)) 
      (ignoreSmallTerms n b (>maxUsedIndex b ≤⟨ right-≤-max {>maxUsedIndex b} {>maxUsedIndex a} ⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎))
  
  missMisses : (a : freeBATerms ℕ) → (miss a) ignores a
  missMisses a = ignoreSmallTerms (>maxUsedIndex a) a (0 , refl) 

isRight : {A B : Type} → A ⊎ B → Bool
isRight (inl _) = false
isRight (inr _) = true 

module deriveProblem (sd : StoneDualityAxiom) (wlpo : WLPO) where

  decider : binarySequence → Bool
  decider α = isRight (wlpo α) 

  deciderZeroSeq=False : decider zeroSequence ≡ false
  deciderZeroSeq=False = case wlpo zeroSequence return (λ x → isRight x ≡ false) of λ { 
    (inl _) → refl; 
    (inr x) → ex-falso (x (λ n → refl)) } 

  deciderδn=true : (n : ℕ) → decider (δ n) ≡ true
  deciderδn=true n = case wlpo (δ n) return (λ x → isRight x ≡ true) of λ { 
    (inl x) → ex-falso (true≢false $
      true  ≡⟨ sym (δnn=true n) ⟩ δ n n ≡⟨ x n ⟩ false ∎ ) ;
    (inr x) → refl } 

  sdAtCantor : ⟨ freeBA ℕ ⟩ ≃ (Sp (freeℕCP) → Bool)
  sdAtCantor .fst = evaluationMap freeℕCP
  sdAtCantor .snd = sd freeℕCP 

  underlyingTerm : ⟨ freeBA ℕ ⟩
  underlyingTerm = invEq sdAtCantor (decider ∘ Iso.inv freeℕUP) 
  
  decidingIsEvaluating : (α : binarySequence) → decider α ≡  evaluate α $cr underlyingTerm
  decidingIsEvaluating α = 
    decider α 
      ≡⟨ cong decider (sym $ Iso.ret freeℕUP α) ⟩ 
    decider (Iso.inv freeℕUP (evaluate α)) 
      ≡⟨ sym (funExt⁻ (secEq sdAtCantor (decider ∘ Iso.inv freeℕUP)) (evaluate α)) ⟩
    evaluate α $cr underlyingTerm ∎ 
  
  module problemTerm (representative : freeBATerms ℕ) (πr=term : fst includeBATermsSurj representative ≡ underlyingTerm) where
  
    problemSequence : binarySequence
    problemSequence = miss representative

    modulusDecider : ℕ
    modulusDecider = >maxUsedIndex representative

    deciderProblem=True : decider problemSequence ≡ true
    deciderProblem=True = deciderδn=true modulusDecider

    representativeEvaluatesAsZero : problemSequence $freeℕ representative ≡ zeroSequence $freeℕ representative  
    representativeEvaluatesAsZero = missMisses representative 
  
    deciderProblem=False : decider problemSequence ≡ false
    deciderProblem=False = 
      decider problemSequence 
        ≡⟨ decidingIsEvaluating problemSequence ⟩ 
      evaluate problemSequence $cr underlyingTerm
        ≡⟨ cong (λ e → evaluate problemSequence $cr e) (sym πr=term) ⟩ 
      problemSequence $freeℕ representative
        ≡⟨ missMisses representative ⟩ 
      zeroSequence $freeℕ representative
        ≡⟨ cong (λ e → evaluate zeroSequence $cr e) πr=term ⟩ 
      evaluate zeroSequence $cr underlyingTerm
        ≡⟨ sym $ decidingIsEvaluating zeroSequence  ⟩ 
      decider zeroSequence
        ≡⟨ deciderZeroSeq=False ⟩ 
      false ∎ 
    
    contradictionWithTerm : ⊥
    contradictionWithTerm = false≢true $ sym deciderProblem=False ∙ deciderProblem=True

  contradiction : ⊥
  contradiction = PT.rec isProp⊥ 
    (uncurry problemTerm.contradictionWithTerm)  
    (snd includeBATermsSurj underlyingTerm) 

SD→¬WLPO : StoneDualityAxiom → ¬ WLPO
SD→¬WLPO = deriveProblem.contradiction 
