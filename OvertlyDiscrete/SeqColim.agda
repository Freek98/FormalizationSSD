module OvertlyDiscrete.SeqColim where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinSet
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit 
open import Cubical.HITs.PropositionalTruncation

module SequentialColimitOfFiniteTypes 
  (X : ℕ → Type) (Xmap : {n : ℕ} → X n → X (suc n))
  (isFin : (n : ℕ) → isFinSet (X n)) where

  open Sequence 

  Xseq : Sequence _
  Xseq .Sequence.obj = X
  Xseq .Sequence.map = Xmap 

  iterMap : (n m : ℕ) → X n  → X (m + n) 
  iterMap n zero x = x
  iterMap n (suc m) x = Xmap (iterMap n m x) 

  ιnm : {n m : ℕ} → (n ≤ m) → X n → X m 
  ιnm {n} {m} (d , d+n=m) x = subst X d+n=m (iterMap n d x) 

  X∞ : Type 
  X∞ = SeqColim Xseq

  EqWitness : {n m : ℕ} → (x : X n) → (y : X m) → Type
  EqWitness {n = n} {m = m} x y = 
    Σ[ k ∈ ℕ ] Σ[ n≤k ∈ (n ≤ k)] Σ[ m≤k ∈ (m ≤ k)] ιnm n≤k x ≡ ιnm m≤k y 

  EqWitness-Increase : {n : ℕ} → (x : X n) → EqWitness x (Xmap x)
  EqWitness-Increase {n = n} x = suc n , ≤-sucℕ , ≤-refl , refl 

  EqWitness-trans-inc : {n m : ℕ} → (x : X n) → (y : X m) → EqWitness x y → EqWitness x (Xmap y)
  EqWitness-trans-inc x y (k , n≤k , m≤k , ιx=ιy) = suc k , {!  !} , {! !} , {! !} 

  EqWitness-trans : {n m k : ℕ} → (x : X n) → (y : X m) → (z : X k) → 
    EqWitness x y → EqWitness y z → EqWitness x z 
  EqWitness-trans x y z (l , n≤l , m≤l , ιx=ιy) (r , m≤r , k≤r , ιy=ιz) = 
    max l r , ≤-trans n≤l left-≤-max , ≤-trans k≤r (right-≤-max {m = l}) , 
    (ιnm _ x  ≡⟨ {! ιx=ιy !} ⟩ ιnm _ y ≡⟨ {! ιy=ιz !} ⟩ ιnm _ z ∎  )

  code : (n : ℕ) → (x : X n) (y : X∞) → Type
  code n x (incl y) = ∥ EqWitness x y ∥₁
  code n x (push y i) = {! EqWitness-trans !} 

--  ιnm : {n m : ℕ} → (m ≥ n) → X n → X m 
--  ιnm {n = n} {m = m} (zero , m+n=d) x = subst {x = n} {y = m} X m+n=d x
--  ιnm {n = n} {m = m} (suc d , m+n=d) x = 
--    subst {x = (suc d + n) } {y = m} X m+n=d (map (ιnm {n = n} {m = d + n} (d , refl) x)) 

