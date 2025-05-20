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