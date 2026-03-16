module Countability.Instances where
open import Countability.Properties

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (pathToIso)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Bool.Properties using (isSetBool ; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥ 

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)

open import Cubical.HITs.PropositionalTruncation as PT

open import BasicDefinitions

ℕcount : has-Countability-structure ℕ
ℕcount .fst _ = true
ℕcount .snd .Iso.fun n = n , refl
ℕcount .snd .Iso.inv (n , _) =  n
ℕcount .snd .Iso.sec (n , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
ℕcount .snd .Iso.ret n = refl 

ℕ×ℕCount : has-Countability-structure (ℕ × ℕ)
ℕ×ℕCount = has-Countability-structure-× ℕcount ℕcount 

ℕ×ℕ-Diag-Count : has-Countability-structure (Σ[ (n , m) ∈ ℕ × ℕ ] ((n ≡ m) → ⊥))
ℕ×ℕ-Diag-Count = has-Countability-structure-Iso (has-Countability-structure-Σ-Bool P ℕ×ℕCount) (invIso ℕ×ℕ-Diag≃ΣℕP) where
  P : ℕ × ℕ → Bool
  P (n , m) = not (n ≡ᵇ m)
  ℕ×ℕ-Diag≃ΣℕP : Iso (Σ[ (n , m)  ∈ ℕ × ℕ ] ((n ≡ m) → ⊥)) (Σ[ p ∈ (ℕ × ℕ) ] P p ≡ true)
  ℕ×ℕ-Diag≃ΣℕP .Iso.fun ((n , m) , n≢m) = (n , m) , ¬false→true (not (n ≡ᵇ m)) λ n≡ᵇm → n≢m {!   !}
  ℕ×ℕ-Diag≃ΣℕP .Iso.inv ((n , m) , Pnm=t) = (n , m) , λ n=m → {! case (discreteℕ n m) of ?  !} 
  ℕ×ℕ-Diag≃ΣℕP .Iso.sec _ = Σ≡Prop (λ _ → isSetBool _ _) refl
  ℕ×ℕ-Diag≃ΣℕP .Iso.ret _ = Σ≡Prop (λ _ → isPropΠ λ _ → isProp⊥) refl 
  



