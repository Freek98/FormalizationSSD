{-# OPTIONS --cubical --guardedness #-}

module Boole.BoolRingUnivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Function
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Reflection.RecordEquiv
private
  variable
    ℓ  : Level
    ℓ' : Level

IsBoolRingHom : {A : Type ℓ} → {B : Type ℓ'} → (Astr : BooleanRingStr A) → 
                (f : A → B)   → (Bstr : BooleanRingStr B) → 
                Type _
IsBoolRingHom Astr f Bstr = IsCommRingHom (BooleanRingStr→CommRingStr Astr) 
                                        f (BooleanRingStr→CommRingStr Bstr)

IsBoolRingEquiv : {A : Type ℓ} → {B : Type ℓ'} → (Astr : BooleanRingStr A) → 
                  (e : A ≃ B)  → (Bstr : BooleanRingStr B) → 
                  Type _
IsBoolRingEquiv Astr e Bstr = 
  IsBoolRingHom Astr (fst e) Bstr

unquoteDecl IsBooleanRingIsoΣ = declareRecordIsoΣ IsBooleanRingIsoΣ (quote IsBooleanRing)

isPropIsBooleanRing : {B : Type ℓ} → 
   {𝟘 𝟙 : B} {_+_ _·_ : B → B → B} { -_ : B → B} → 
   isProp (IsBooleanRing 𝟘 𝟙 _+_ _·_ -_)

isPropIsBooleanRing {B = B} {_·_ = _·h_} = isOfHLevelRetractFromIso 1 IsBooleanRingIsoΣ 
  (isPropΣ (isPropIsCommRing _ _ _ _ _) f) where 
  -- TODO clean this up, look at how isPropRing works, it's shorter
--  (λ ring → isPropΠ2 (λ _ _ → is-set ring _ _)))
--  However, is-set is apparently part of the IsRing, but not of isCommRing
    open CommRingStr 
    f : IsCommRing _ _ _ _·h_ _ → isProp ((x : B) → (x ·h x) ≡ x) 
    f isCR p q = funExt λ x → is-set CRstr (x ·h x) x (p x) (q x) where
      CRstr : CommRingStr B
      CRstr .0r  = _
      CRstr .1r  = _
      CRstr ._+_ = _
      CRstr ._·_ = _
      CRstr .-_  = _
      CRstr .isCommRing = isCR 

𝒮ᴰ-BooleanRing : DUARel (𝒮-Univ ℓ) BooleanRingStr ℓ
𝒮ᴰ-BooleanRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsBoolRingEquiv
    (fields:
      data[  𝟘  ∣ null ∣ pres0 ]
      data[  𝟙  ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin  ∣ pres+ ]
      data[ _·_ ∣ bin  ∣ pres· ]
      data[ -_  ∣ autoDUARel _ _ ∣ pres- ]
      prop[ isBooleanRing ∣ (λ _ _ → isPropIsBooleanRing) ])
 where
  open BooleanRingStr
  open IsCommRingHom
  
  null = autoDUARel (𝒮-Univ _) (λ a → a)
  bin  = autoDUARel (𝒮-Univ _) (λ a → a → a → a)

BoolRingEquiv : {ℓ ℓ' : Level} (A : BooleanRing ℓ) (B : BooleanRing ℓ') → Type _
BoolRingEquiv A B = Σ[ e ∈ ⟨ A ⟩ ≃ ⟨ B ⟩ ] IsBoolRingEquiv (snd A) e (snd B)

opaque 
  BoolRingPath : (R S : BooleanRing ℓ) → BoolRingEquiv R S ≃ (R ≡ S)
  BoolRingPath = ∫ 𝒮ᴰ-BooleanRing .UARel.ua
  
  BoolRingPathInvRefl≡Idfun : (B : BooleanRing ℓ) → fst (fst ((fst $ invEquiv $ BoolRingPath B B) refl)) ≡ idfun ⟨ B ⟩ 
  BoolRingPathInvRefl≡Idfun B = funExt transportRefl
  
  uaBoolRing : {A B : BooleanRing ℓ} → BoolRingEquiv A B → A ≡ B
  uaBoolRing {A = A} {B = B} = equivFun (BoolRingPath A B)


{-
open Iso
--isPropIsCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R)
--             → isProp (IsCommRing 0r 1r _+_ _·_ -_)
--isPropIsCommRing 0r 1r _+_ _·_ -_ =
--  isOfHLevelRetractFromIso 1 IsCommRingIsoΣ
--  (isPropΣ (isPropIsRing 0r 1r _+_ _·_ (-_))
--  (λ ring → isPropΠ2 (λ _ _ → is-set ring _ _)))
--  where
--  open IsRing




--  (λ ring → isPropΠ2 (λ _ _ → is-set ring _ _)))
extendEquiv : (A B : BooleanRing ℓ) → CommRingEquiv (BooleanRing→CommRing A) (BooleanRing→CommRing B) ≡ BooleanRingEquiv A B
extendEquiv A B = refl 

extendEquality : (A B : BooleanRing ℓ) → ((BooleanRing→CommRing A) ≡ (BooleanRing→CommRing B)) → A ≡ B
extendEquality A B x = ΣPathP (cong fst x , f) where
  open BooleanRingStr
  f : PathP (λ i → BooleanRingStr ( fst (x i))) (snd A) (snd B)
  f i .𝟘 = _
  f i .𝟙 = _
  f i ._+_ = _
  f i ._·_ = _
  - f i = _
  f i .isBooleanRing = isPropIsBooleanRing {! isBooleanRing $ snd A !} {! isBooleanRing $ snd B !} i


--ΣPathP
BooleanRingPath : (R S : BooleanRing ℓ) → BooleanRingEquiv R S ≃ (R ≡ S)
BooleanRingPath R S = subst (λ P → P ≃ (R ≡ S)) (extendEquiv R S) 
  ({! fst $ CommRingPath (BooleanRing→CommRing R) (BooleanRing→CommRing S) !} , {! !})

uaBooleanRing : {A B : BooleanRing ℓ} → BooleanRingEquiv A B → A ≡ B
uaBooleanRing {A = A} {B = B} = equivFun (BooleanRingPath A B)
-}
