open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Logic.Adjoint (Atom : Set) where

  open import Logic.Core.Props Atom public
  open import Logic.Core.Modes public
  open import Logic.Core.Contexts Atom public

  data _⊢ⁱ_ : Context n → (Prop × Mode) → Set where

    id : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ' → cWeakenable Δ'
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A , m ⟩

    cut : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → m ≥ k
      → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩
      → (⟨ A , m ⟩ ∷ Δ₂₃) ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊕R₁ : Δ ⊢ⁱ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊕ B , m ⟩

    ⊕R₂ : Δ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊕ B , m ⟩

    ⊕L : mayConsume Δ ⟨ A ⊕ B , m ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩ → (⟨ B , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    &R : Δ ⊢ⁱ ⟨ A , m ⟩ → Δ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A & B , m ⟩

    &L₁ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    &L₂ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  (⟨ B , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊗R : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩ → Δ₂₃ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊗ B , m ⟩

    ⊗L : mayConsume Δ ⟨ A ⊗ B , m ⟩ Δ'
      → (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊸R : (⟨ A , m ⟩ ∷ Δ) ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊸ B , m ⟩

    ⊸L : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → mayConsume Δ₁₂ ⟨ A ⊸ B , m ⟩ Δ₁₂'
      → mayConsume Δ₂₃ ⟨ A ⊸ B , m ⟩ Δ₂₃'
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩
      → (⟨ B , m ⟩ ∷ Δ₂₃) ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    𝟙R : cWeakenable Δ
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ 𝟙 , m ⟩

    𝟙L : mayConsume Δ ⟨ 𝟙 , m ⟩ Δ' → Δ' ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ↓R : merge Δ₁ Δ₂ Δ
      → Δ₁ ≥ᶜ m 
      → cWeakenable Δ₂
      → Δ₁ ⊢ⁱ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ ↓[ m ][ k ] A , k ⟩

    ↓L : mayConsume Δ ⟨ ↓[ m ][ k ] A , m ⟩ Δ'
      → (⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , l ⟩

    ↑R : Δ ⊢ⁱ ⟨ A , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ ↑[ m ][ k ] A , k ⟩

    ↑L : mayConsume Δ ⟨ ↑[ k ][ m ] A , k ⟩ Δ' → k ≥ l
      → (⟨ A , k ⟩ ∷ Δ') ⊢ⁱ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , l ⟩

  data _⊢ᵉ_ : Context n → (Prop × Mode) → Set where

    id : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ' → exh Δ'
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A , m ⟩

    cut : merge Δ₁ Δ₂ Δ
      → Δ₁ ≥ᶜ m → m ≥ k
      → Δ₁ ⊢ᵉ ⟨ A , m ⟩
      → (⟨ A , m ⟩ ∷ Δ₂) ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    weak : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ'
      → mWeakenable m → Δ' ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    contr : update Δ ⟨ A , m ⟩ ⟨ A , m ⟩ Δ
      → mContractable m → (⟨ A , m ⟩ ∷ Δ) ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ⊕R₁ : Δ ⊢ᵉ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊕ B , m ⟩

    ⊕R₂ : Δ ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊕ B , m ⟩

    ⊕L : update Δ (⟨ A ⊕ B , m ⟩) (⟨ A ⊕ B , Irrelevant ⟩) Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩ → (⟨ B , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    &R : Δ ⊢ᵉ ⟨ A , m ⟩ → Δ ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A & B , m ⟩

    &L₁ : update Δ ⟨ A & B , m ⟩ ⟨ A & B , Irrelevant ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    &L₂ : update Δ ⟨ A & B , m ⟩ ⟨ A & B , Irrelevant ⟩ Δ'
      →  (⟨ B , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ⊗R : merge Δ₁ Δ₂ Δ
      → Δ₁ ⊢ᵉ ⟨ A , m ⟩ → Δ₂ ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊗ B , m ⟩

    ⊗L : update Δ ⟨ A ⊗ B , m ⟩ ⟨ A ⊗ B , Irrelevant ⟩ Δ'
      → (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ⊸R : (⟨ A , m ⟩ ∷ Δ) ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊸ B , m ⟩

    ⊸L : merge Δ₁ Δ₂ Δ'
      → update Δ ⟨ A ⊸ B , m ⟩ ⟨ A ⊸ B , Irrelevant ⟩ Δ'
      → Δ₁ ≥ᶜ m → Δ₁ ⊢ᵉ ⟨ A , m ⟩
      → (⟨ B , m ⟩ ∷ Δ₂) ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    𝟙R : cWeakenable Δ
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ 𝟙 , m ⟩

    𝟙L : update Δ ⟨ 𝟙 , m ⟩ ⟨ 𝟙 , Irrelevant ⟩ Δ' → Δ' ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ↓R : Δ ≥ᶜ m → Δ ⊢ᵉ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ ↓[ m ][ k ] A , m ⟩

    ↓L : update Δ ⟨ ↓[ m ][ k ] A , m ⟩ ⟨ ↓[ m ][ k ] A , Irrelevant ⟩ Δ'
      → (⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , l ⟩

    ↑R : Δ ⊢ᵉ ⟨ A , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ ↑[ m ][ k ] A , k ⟩

    ↑L : update Δ ⟨ ↑[ k ][ m ] A , k ⟩ ⟨ ↑[ k ][ m ] A , Irrelevant ⟩ Δ'
      → k ≥ l → (⟨ A , k ⟩ ∷ Δ') ⊢ᵉ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , l ⟩ 