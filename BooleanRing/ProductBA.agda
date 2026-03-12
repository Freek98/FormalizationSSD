{-# OPTIONS --guardedness #-}

module BooleanRing.ProductBA where 

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.DirectProd

open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Unit
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group

module BRProduct {ℓ ℓ' : Level} (B : BooleanRing ℓ) (C : BooleanRing ℓ') where
  instance 
    _ = snd B 
    _ = snd C 
  product : BooleanRing (ℓ-max ℓ ℓ')
  product = idemCommRing→BR B×C-CR (uncurry ·IdemProd) where
    B×C-CR : CommRing (ℓ-max ℓ ℓ')
    B×C-CR = (DirectProd-CommRing (BooleanRing→CommRing B) (BooleanRing→CommRing C))
    open CommRingStr (snd B×C-CR)
    ·IdemProd : (b : ⟨ B ⟩) (c : ⟨ C ⟩) → (b , c) · (b , c) ≡ (b , c)
    ·IdemProd b c = cong₂ _,_ 
      (BooleanRingStr.·Idem (snd B) b) 
      (BooleanRingStr.·Idem (snd C) c) 

