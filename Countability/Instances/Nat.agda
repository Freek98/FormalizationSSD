module Countability.Instances.Nat where
open import Countability.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat 
open import Cubical.Data.Bool 
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

ℕcount : has-Countability-structure ℕ
ℕcount .fst _ = true
ℕcount .snd .Iso.fun n = n , refl
ℕcount .snd .Iso.inv (n , _) =  n
ℕcount .snd .Iso.sec (n , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
ℕcount .snd .Iso.ret n = refl

isCountableℕ : is-countable ℕ
isCountableℕ = ∣ ℕcount ∣₁
