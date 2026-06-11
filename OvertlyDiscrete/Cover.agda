{-# OPTIONS --lossy-unification #-}
module OvertlyDiscrete.Cover where
-- Goal of this file: show that sequential colimits of things with a countable cover has a countable cover
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence 
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit
open import Cubical.Relation.Nullary
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat.Order.Recursive using (Decidable→Collapsible)

module (X : ℕ → Type) (


