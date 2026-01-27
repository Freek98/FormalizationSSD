{-
2cp : BooleanRing ℓ-zero
2cp = freeBA ℕ /Im generator 

2→2cp : BoolHom BoolBR 2cp
2→2cp = BoolBR→ 2cp

opaque
  unfolding generator
  unfolding freeBA
  unfolding inducedBAHom
  unfolding QB.inducedHom
  2cp→2 : BoolHom 2cp BoolBR
  2cp→2 = QB.inducedHom {B = freeBA ℕ} {f = generator} BoolBR (inducedBAHom ℕ BoolBR λ n → false) (funExt⁻ (evalBAInduce ℕ BoolBR (λ n → false))) 
  
2→2   : fst (BoolBR→ BoolBR)  ≡ idfun Bool 
2→2  = funExt λ { false → refl
                ; true  → refl } 


free→2 : {A : Type} → BoolHom (freeBA A)  BoolBR
free→2 {A} = (Iso.fun $ freeBA-universal-property A BoolBR) λ _ → false 

freeNonTriv : {A : Type} → nontriv (freeBA A) 
freeNonTriv {A} = map→2→nontriv (freeBA A) free→2

2cpNonTriv : nontriv 2cp
2cpNonTriv = map→2→nontriv 2cp 2cp→2 

private 
  projection : freeBATerms ℕ ↠ ⟨ 2cp ⟩
  projection = compSurjection includeBATermsSurj 
    ((fst $ quotientImageHom ) , quotientImageHomSurjective) 

project : freeBATerms ℕ → ⟨ 2cp ⟩
project = fst projection

projectSurj : isSurjection project
projectSurj = snd projection

quotHom : CommRingHom (BoolCR [ ℕ ]) (BooleanRing→CommRing (2cp))  
quotHom = {! !} -- quotientImageHom -- (freeBA ℕ) generator ∘cr IQ.quotientImageHom (BoolCR [ ℕ ]) _ 


module _ where
  open IsCommRingHom (snd quotHom)
  open BooleanRingStr (snd 2cp)
  open BooleanAlgebraStr 2cp
  open CommRingStr (snd (BoolCR [ ℕ ])) 
  opaque 
    unfolding includeBATermsSurj
    unfolding QB._/Im_
    unfolding QB.quotientImageHom
    unfolding generator

    help+ : (x y : freeBATerms ℕ) → (project x ≡ 𝟘 ) ⊎ (project x ≡ 𝟙) → (project y ≡ 𝟘) ⊎ (project y ≡ 𝟙) → (project (x +T y) ≡ 𝟘)  ⊎ (project (x +T y) ≡ 𝟙)
    help+ x y xdec ydec = transport (cong (λ a → (a ≡ 𝟘) ⊎ (a ≡ 𝟙)) (sym $ pres+ (includeTerm x) (includeTerm y))) 
                          (01+closed {B = 2cp} (project x) (project y) xdec ydec) 
    {- 
    help· : (x y : freeBATerms ℕ) → (project x ≡ 𝟘 ) ⊎ (project x ≡ 𝟙) → (project y ≡ 𝟘) ⊎ (project y ≡ 𝟙) → (project (x ·T y) ≡ 𝟘)  ⊎ (project (x ·T y) ≡ 𝟙)
    help· x y xdec ydec = transport (cong (λ a → (a ≡ 𝟘) ⊎ (a ≡ 𝟙)) (sym $ pres· (includeTerm x) (includeTerm y))) (01·closed {B = 2cp} (project x) (project y) xdec ydec) 
    
    help- : (x : freeBATerms ℕ) → (project x ≡ 𝟘 ) ⊎ (project x ≡ 𝟙) → (project (-T x) ≡ 𝟘)  ⊎ (project (-T x) ≡ 𝟙)
    help- x xdec = transport (cong (λ a → (a ≡ 𝟘) ⊎ (a ≡ 𝟙)) (sym $ pres- (includeTerm x))) (01-closed {B = 2cp} (project x) xdec ) 
  opaque
    unfolding includeBATermsSurj
    unfolding generator 
    helpmax2freeBA : (x : freeBATerms ℕ) → (project x ≡ 𝟘) ⊎ (project x ≡ 𝟙)
    helpmax2freeBA (Tvar n) = inl $(project) (Tvar n) ≡⟨⟩ 
                                   quotientImageHom $cr fst includeBATermsSurj (Tvar n) ≡⟨⟩
                                   quotientImageHom $cr (generator n) ≡⟨ zeroOnImage n ⟩
                                   𝟘 ∎ 
    helpmax2freeBA (Tconst false) = inl $ project (Tconst false) ≡⟨⟩ 
                                          quotHom $cr 0r ≡⟨ pres0 ⟩
                                          𝟘 ∎
    helpmax2freeBA (Tconst true ) = inr $ project (Tconst true) ≡⟨⟩ 
                                          quotHom $cr 1r ≡⟨ pres1 ⟩
                                          𝟙 ∎
    helpmax2freeBA (x +T y) = help+ x y (helpmax2freeBA x) (helpmax2freeBA y)
    helpmax2freeBA (-T x)   = help- x   (helpmax2freeBA x) 
    helpmax2freeBA (x ·T y) = help· x y (helpmax2freeBA x) (helpmax2freeBA y) 

  max2cp : max2 2cp 
  max2cp b = PT.rec (λ { (inl b=0) (inl b=0') → cong inl $ BooleanRingStr.is-set (snd $ 2cp) b 𝟘 b=0 b=0'
                       ; (inl b=0) (inr b=1 ) → ex-falso (2cpNonTriv (sym b=0 ∙ b=1))
                       ; (inr b=1) (inl b=0 ) → ex-falso (2cpNonTriv (sym b=0 ∙ b=1))
                       ; (inr b=1) (inr b=1') → cong inr $ BooleanRingStr.is-set (snd $ 2cp) b 𝟙 b=1 b=1' }) 
                    (λ { (bTerm , bTerm=b) → transport (cong (λ a → (a ≡ 𝟘) ⊎ (a ≡ 𝟙)) bTerm=b) (helpmax2freeBA bTerm) }) (projectSurj b) 


2=2cp : BooleanRingEquiv BoolBR 2cp 
2=2cp = {! !} 
--BooleanRingEquiv.fst.fst 2=2cp = fst $ BoolBR→ 2cp
--BooleanRingEquiv.fst.snd 2=2cp = BoolBRCharacterisationHelper 2cp 2cpNonTriv max2cp
--BooleanRingEquiv.snd 2=2cp = snd $ BoolBR→ 2cp 
-}
-}
--open import QuotientBool
--open import NaturalNumbersProperties.NBijection
--import Cubical.HITs.SetQuotients as SQ
-- (WLPO' : ((α : binarySequence) → Dec (∀ (n : ℕ ) → α n ≡ false) ))

--_>B_ : ℕ → ℕ → Bool
--m >B n = Dec→Bool (<Dec n m) 

--binarySequence' : Type _
--binarySequence' = Σ[ α ∈ (ℕ → Type) ] ((n : ℕ) → Dec (α n))


--switch'→ : binarySequence' → binarySequence 
--switch'→ (α , isdec ) n = case isdec n of λ { (yes _) → true
--                                            ; (no  _) → false } 
--
--boolDecEquality : (b : Bool) → Dec (b ≡ true) 
--boolDecEquality false = no false≢true
--boolDecEquality true = yes refl
--
--
--switch→' : binarySequence → binarySequence' 
--fst (switch→' α) n = α n ≡ true
--snd (switch→' α) n = boolDecEquality (α n) 

--hasCountableStructure : Type → Type
--hasCountableStructure A = Σ[ D ∈ binarySequence ] Iso A ( Σ[ n ∈ ℕ ] (D n ≡ true))
--
--isCountable : Type → Type 
--isCountable A = ∥ hasCountableStructure A ∥₁
--
--BooleωStruct : Type → Type ℓ-zero 
--BooleωStruct B = Σ[ f ∈ (ℕ → ⟨ freeBA ℕ ⟩) ]  
--                 Iso B ⟨ freeBA ℕ /Im f ⟩
