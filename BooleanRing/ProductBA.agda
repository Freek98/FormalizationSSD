{-# OPTIONS --lossy-unification #-}
module BooleanRing.ProductBA where 

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

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
open import CategoryTheory.StuffFromStoneAboutBAs
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Category

private 
  variable ℓ ℓ' ℓ'' : Level

module BRProduct (B : BooleanRing ℓ) (C : BooleanRing ℓ') where
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
  open IsCommRingHom ⦃...⦄
  πB : BoolHom product B
  πB .fst = fst
  πB .snd .pres0 = refl
  πB .snd .pres1 = refl
  πB .snd .pres+ _ _ = refl
  πB .snd .pres· _ _ = refl
  πB .snd .pres- _ = refl 
  
  πC : BoolHom product C
  πC .fst = snd
  πC .snd .pres0 = refl
  πC .snd .pres1 = refl
  πC .snd .pres+ _ _ = refl
  πC .snd .pres· _ _ = refl
  πC .snd .pres- _ = refl 
  
  module UP {D : BooleanRing ℓ''} (f : BoolHom D B) (g : BoolHom D C) where
    instance 
      _ = snd f 
      _ = snd g 
    ⟨f,g⟩ : BoolHom D product 
    ⟨f,g⟩ .fst x = (f $cr x) , (g $cr x)
    ⟨f,g⟩ .snd .pres0     = cong₂ _,_ pres0 pres0
    ⟨f,g⟩ .snd .pres1     = cong₂ _,_ pres1 pres1
    ⟨f,g⟩ .snd .pres+ x y = cong₂ _,_ (pres+ x y) (pres+ x y)
    ⟨f,g⟩ .snd .pres· x y = cong₂ _,_ (pres· x y) (pres· x y)
    ⟨f,g⟩ .snd .pres- x   = cong₂ _,_ (pres- x) (pres- x) 

    extensionπB : πB ∘cr ⟨f,g⟩ ≡ f
    extensionπB = CommRingHom≡ refl 
    extensionπC : πC ∘cr ⟨f,g⟩ ≡ g
    extensionπC = CommRingHom≡ refl 

    uniqueness : (h : BoolHom D product) → (πB ∘cr h ≡ f) → (πC ∘cr h ≡ g) → ⟨f,g⟩ ≡ h
    uniqueness h Bh=f Ch=g = CommRingHom≡ (funExt λ d → cong₂ _,_ 
      (cong (λ k → fst k d) (sym Bh=f)) (cong (λ k → fst k d) (sym Ch=g))) 
--    isContr Σ[ fg
    --isBinProduct = ∀ {z : ob} (f₁ : Hom[ z , x ]) (f₂ : Hom[ z , y ]) →
    --    ∃![ f ∈ Hom[ z , x×y ] ] (f ⋆ π₁ ≡ f₁) × (f ⋆ π₂ ≡ f₂)



module BACatProduct {ℓ : Level} (B : BooleanRing ℓ) (C : BooleanRing ℓ) where
    open BinProduct
    open BRProduct B C 
    open UP
    open Category 
    catProduct : BinProduct BACat B C 
    catProduct .binProdOb = product
    catProduct .binProdPr₁ = πB
    catProduct .binProdPr₂ = πC
    catProduct .univProp f g .fst .fst = ⟨f,g⟩ f g
    catProduct .univProp f g .fst .snd = extensionπB f g , extensionπC f g
    catProduct .univProp f g .snd (h , Bh=f , Ch=g) = Σ≡Prop 
      (λ _ → isProp× (isSetHom BACat _ _) (isSetHom BACat _ _)) 
      -- Note that this argument works for any category, 
      -- so maybe this should be generalized to a smart constructor.
      (uniqueness f g h Bh=f Ch=g)

_×BR_ : (B : BooleanRing ℓ) (C : BooleanRing ℓ') → BooleanRing (ℓ-max ℓ ℓ')
_×BR_ = BRProduct.product

induceProdMapBR : {B : BooleanRing ℓ} → {C : BooleanRing ℓ'} → {D : BooleanRing ℓ''} → 
                   BoolHom D B → BoolHom D C → BoolHom D (B ×BR C)
induceProdMapBR {B = B} {C = C} = BRProduct.UP.⟨f,g⟩ B C
