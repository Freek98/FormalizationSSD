
module Countability.Instances.Nat where
open import Countability.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (pathToIso)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming ( _≡ᵇ_ to _≡ℕ_ )
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Bool.Properties using (isSetBool ; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)

open import Cubical.HITs.PropositionalTruncation as PT

ℕcount : has-Countability-structure ℕ
ℕcount .fst _ = true
ℕcount .snd .Iso.fun n = n , refl
ℕcount .snd .Iso.inv (n , _) =  n
ℕcount .snd .Iso.sec (n , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
ℕcount .snd .Iso.ret n = refl

isCountableℕ : is-countable ℕ
isCountableℕ = ∣ ℕcount ∣₁
