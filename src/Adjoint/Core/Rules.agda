open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Vec
open import Data.Nat

module Adjoint.Core.Rules 
  (Atom : Set)
  (Mode : Set)
  (mWeakenable : Mode → Set)
  (mContractable : Mode → Set)
  (mHarmless : Mode → Set)
  (_∙_⇒_ : Mode → Mode → Mode → Set)
  (_≥_ : Mode → Mode → Set) 
  where
  
  open import Adjoint.Core.Props Atom Mode
  open import Adjoint.Core.Contexts 
    Atom 
    Mode  
    mWeakenable 
    mContractable 
    mHarmless 
    _∙_⇒_ 
    _≥_ 

  private
    variable
      n : ℕ
      Δ Δ' Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃' : Context n
      m k l : Mode
      A B C : Prop 
  
  data _⊢_ : Context n → ModedProp → Set where

    id : update Δ ⟨ A , m ⟩ ⟨ A , k ⟩ Δ' → cWeakenable Δ' → mHarmless k
      ----------------------------------------------------------
      → Δ ⊢ ⟨ A , m ⟩

    cut : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → m ≥ k
      → cContractable Δ₂
      → Δ₁₂ ⊢ ⟨ A , m ⟩
      → (⟨ A , m ⟩ ∷ Δ₂₃) ⊢ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , k ⟩

    ⊕R₁ : Δ ⊢ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ A ⊕ B , m ⟩

    ⊕R₂ : Δ ⊢ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ A ⊕ B , m ⟩

    ⊕L : mayConsume Δ ⟨ A ⊕ B , m ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩ → (⟨ B , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , k ⟩

    &R : Δ ⊢ ⟨ A , m ⟩ → Δ ⊢ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ A & B , m ⟩

    &L₁ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , k ⟩

    &L₂ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  (⟨ B , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , k ⟩

    ⊗R : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → cContractable Δ₂
      → Δ₁₂ ⊢ ⟨ A , m ⟩ → Δ₂₃ ⊢ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ A ⊗ B , m ⟩

    ⊗L : mayConsume Δ ⟨ A ⊗ B , m ⟩ Δ'
      → (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , k ⟩

    ⊸R : (⟨ A , m ⟩ ∷ Δ) ⊢ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ A ⊸ B , m ⟩

    ⊸L : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → mayConsume Δ₁₂ ⟨ A ⊸ B , m ⟩ Δ₁₂'
      → mayConsume Δ₂₃ ⟨ A ⊸ B , m ⟩ Δ₂₃'
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → cContractable Δ₂
      → Δ₁₂ ⊢ ⟨ A , m ⟩
      → (⟨ B , m ⟩ ∷ Δ₂₃) ⊢ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , k ⟩

    𝟙R : cWeakenable Δ
      ----------------------------------------------------------
      → Δ ⊢ ⟨ 𝟙 , m ⟩

    𝟙L : mayConsume Δ ⟨ 𝟙 , m ⟩ Δ' → Δ' ⊢ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , k ⟩

    ↓R : merge Δ₁ Δ₂ Δ
      → Δ₁ ≥ᶜ m 
      → cWeakenable Δ₂
      → Δ₁ ⊢ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ ↓[ k ][ m ] A , k ⟩

    ↓L : mayConsume Δ ⟨ ↓[ k ][ m ] A , k ⟩ Δ'
      → (⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , l ⟩

    ↑R : Δ ⊢ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ ↑[ k ][ m ] A , k ⟩

    ↑L : mayConsume Δ ⟨ ↑[ k ][ m ] A , k ⟩ Δ' → k ≥ l
      → (⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ ⟨ C , l ⟩
 