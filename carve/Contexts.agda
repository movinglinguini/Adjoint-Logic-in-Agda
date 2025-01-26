open import Data.Vec
open import Data.Nat hiding (_≥_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Modes
open import Props

module Contexts where

  Context : ∀ ( n : ℕ ) → Set
  Context n = Vec (Prop × Mode) n

  variable
    n : ℕ
    Δ Δ' Δ₁ Δ₂ Δ₃ Δ₂' Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃'  : Context n

  data cWeakenable : Context n → Set where
    weak/n : cWeakenable []
    weak/c : cWeakenable Δ → mWeakenable m → cWeakenable (⟨ A , m ⟩ ∷ Δ)

  data cContractable : Context n → Set where
    cont/n : cContractable []
    cont/c : cContractable Δ → mContractable m → cContractable (⟨ A , m ⟩ ∷ Δ)

  data exh : Context n → Set where
    exh/n : exh []
    exh/c : exh Δ → harmless m → exh (⟨ A , m ⟩ ∷ Δ)

  data _≥ᶜ_ : Context n → Mode → Set where
    N : [] ≥ᶜ m
    S : Δ ≥ᶜ k → m ≥ k → (⟨ A , m ⟩ ∷ Δ) ≥ᶜ k

  data merge : Context n → Context n → Context n → Set where
    mg/n : merge [] [] []
    mg/c : merge Δ₁ Δ₂ Δ → m₁ ∙ m₂ ⇒ m
      → merge (⟨ A , m₁ ⟩ ∷ Δ₁) (⟨ A , m₂ ⟩ ∷ Δ₂) (⟨ A , m ⟩ ∷ Δ)

  data update : Context n → Prop × Mode → Prop × Mode → Context n → Set where
    N : update (⟨ A , m ⟩ ∷ Δ) (⟨ A , m ⟩) (⟨ B , k ⟩) (⟨ B , k ⟩ ∷ Δ)

    S : update Δ (⟨ A , m ⟩) (⟨ B , k ⟩) Δ'
      → update (⟨ C , l ⟩ ∷ Δ) (⟨ A , m ⟩) (⟨ B , k ⟩) (⟨ C , l ⟩ ∷ Δ')

  data mayConsume : Context n → Prop × Mode → Context n → Set where
    yea : update Δ (⟨ A , m ⟩) (⟨ A , Irrelevant ⟩) Δ'
      → mayConsume Δ ⟨ A , m ⟩ Δ'

    nay : update Δ (⟨ A , m ⟩) (⟨ A , m ⟩) Δ → mContractable m
      → mayConsume Δ ⟨ A , m ⟩ Δ

  ----------------------------------------------------------
  -- Properties of context predicates
  ----------------------------------------------------------

  exh_to_cWeakenable : exh Δ → cWeakenable Δ
  exh_to_cWeakenable exh/n = weak/n 
  exh_to_cWeakenable (exh/c E1 T1) = weak/c (exh_to_cWeakenable E1) (harmless_to_mWeakenable T1)

  exh_to_cContractable : exh Δ → cContractable Δ
  exh_to_cContractable exh/n = cont/n 
  exh_to_cContractable (exh/c E1 T1) = cont/c (exh_to_cContractable E1) (harmless_to_mContractable T1)

  ----------------------------------------------------------
  -- Properties of merge
  ----------------------------------------------------------

  merge-comm : merge Δ₁ Δ₂ Δ → merge Δ₂ Δ₁ Δ
  merge-comm mg/n = mg/n
  merge-comm (mg/c D T) = mg/c (merge-comm D) (∙-comm T)

  merge-func : merge Δ₁ Δ₂ Δ → merge Δ₁ Δ₂ Δ' → Δ ≡ Δ'
  merge-func mg/n mg/n = refl
  merge-func (mg/c M1 T1) (mg/c M2 T2)
    with refl ← merge-func M1 M2
       | refl ← ∙-func T1 T2 = refl

  data mergeAssoc : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₁₂ Δ₃ Δ → Set where
    merge/assoc : {D1 : merge Δ₁ Δ₂ Δ₁₂} {D2 : merge Δ₁₂ Δ₃ Δ} → merge Δ₁ Δ₂₃ Δ → merge Δ₂ Δ₃ Δ₂₃
      → mergeAssoc D1 D2

  merge-assoc : ∀ (D1 : merge Δ₁ Δ₂ Δ₁₂) (D2 : merge Δ₁₂ Δ₃ Δ) → mergeAssoc D1 D2
  merge-assoc mg/n mg/n = merge/assoc mg/n mg/n
  merge-assoc (mg/c D1 T1) (mg/c D2 T2)
    with merge/assoc M3 M4 ← merge-assoc D1 D2
       | ∙/assoc T3 T4 ← ∙-assoc T1 T2 = merge/assoc (mg/c M3 T3) (mg/c M4 T4)

  merge-cancl : merge Δ₁ Δ₂ Δ → merge Δ₁ Δ₂' Δ → Δ₂ ≡ Δ₂'
  merge-cancl mg/n mg/n = refl
  merge-cancl (mg/c M1 T1) (mg/c M2 T2)
    with refl ← merge-cancl M1 M2 
       | refl ← •-cancl T1 T2 = refl

  data mergeGetId : Context n → Set where
    merge/getid : merge Δ Δ' Δ → exh Δ' → mergeGetId Δ

  merge-getid : ∀ ( Δ : Context n ) → mergeGetId Δ
  merge-getid [] = merge/getid mg/n exh/n
  merge-getid (⟨ A , m ⟩ ∷ Δ) with
    merge/getid M1 E1 ← merge-getid Δ
      | ∙/getid M2 H1 ← ∙-getid m = merge/getid (mg/c M1 M2) (exh/c E1 H1)