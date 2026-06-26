module Countability.Instances.BinaryProduct where 

open import Countability.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open Iso 
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import Cubical.Data.Nat.Bijections.Product 
open import BinarySequences.Definitions
open import Cubical.HITs.PropositionalTruncation as PT

module ΣℕProdBinarySequence (α β : binarySequence) where
  γ : binarySequence
  γ n = α (fst (inv ℕ×ℕ≅ℕ n)) and β (snd (inv ℕ×ℕ≅ℕ n))

  Σℕα×Σℕβ=Σℕγ : Iso (Σℕ1 α × Σℕ1 β) (Σℕ1 γ)

  fun Σℕα×Σℕβ=Σℕγ ((n , p) , (m , q)) = k , γk=1
    where
      k = fun ℕ×ℕ≅ℕ (n , m)
      eq : inv ℕ×ℕ≅ℕ k ≡ (n , m)
      eq = ret ℕ×ℕ≅ℕ (n , m)

      γk=1 : γ k ≡ true
      γk=1 =
        α (fst (inv ℕ×ℕ≅ℕ k)) and β (snd (inv ℕ×ℕ≅ℕ k))
          ≡⟨ cong₂ (λ x y → α x and β y) (cong fst eq) (cong snd eq) ⟩
        α n and β m
          ≡⟨ cong₂ _and_ p q ⟩
        true and true
          ≡⟨⟩
        true ∎

  inv Σℕα×Σℕβ=Σℕγ (k , r) = (n , fst αn=βm=1) , (m , snd αn=βm=1)
    where
      n = fst (inv ℕ×ℕ≅ℕ k)
      m = snd (inv ℕ×ℕ≅ℕ k)
      
      and-elim : (a b : Bool) → (a and b ≡ true) → (a ≡ true) × (b ≡ true)
      and-elim false false x = ex-falso $ false≢true x
      and-elim false true  x = ex-falso $ false≢true x
      and-elim true  false x = ex-falso $ false≢true x
      and-elim true  true  _ = refl , refl 

      αn=βm=1 : (α n ≡ true) × (β m ≡ true)
      αn=βm=1 = and-elim (α n) (β m) r 

  sec Σℕα×Σℕβ=Σℕγ (k , r) = ΣPathP (sec ℕ×ℕ≅ℕ k , toPathP (isSetBool _ _ _ _))

  ret Σℕα×Σℕβ=Σℕγ ((n , p) , (m , q)) =
    ΣPathP (ΣPathP (cong fst eq , toPathP (isSetBool _ _ _ _)) ,
            ΣPathP (cong snd eq , toPathP (isSetBool _ _ _ _)))
    where
      eq : inv ℕ×ℕ≅ℕ (fun ℕ×ℕ≅ℕ (n , m)) ≡ (n , m)
      eq = ret ℕ×ℕ≅ℕ (n , m)

countabilityStructureBinaryProduct : {ℓ : Level} → (A B : Type ℓ) → 
  has-Countability-structure A → has-Countability-structure B → 
  has-Countability-structure (A × B)
countabilityStructureBinaryProduct A B (α , A=Σα) (β , B=Σβ) = γ , compIso (prodIso A=Σα B=Σβ) Σℕα×Σℕβ=Σℕγ where 
  open ΣℕProdBinarySequence α β

is-countable-BinaryProduct : {ℓ : Level} → (A B : Type ℓ) → 
  is-countable A → is-countable B → is-countable (A × B)
is-countable-BinaryProduct A B = rec2 squash₁ λ a b → ∣ countabilityStructureBinaryProduct A B a b ∣₁ 
