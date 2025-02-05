open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Logic.Core.Props
open import Logic.Core.Terms

module Logic.Adjoint (Atom : Set) (T : Set) (subst : Prop (Atom) → Term (T) → Prop (Atom))  where

  open import Logic.Core.Modes
  open import Logic.Core.Contexts Atom T

  data _⊢ⁱ_ : Context y n → (Prop (Atom) × Mode) → Set where

    id : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ' → cWeakenable Δ'
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A , m ⟩

    cut : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → m ≥ k
      → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩
      → ⟨ proj₁ Δ₂₃ , (⟨ A , m ⟩ ∷ proj₂ Δ₂₃) ⟩ ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊕R₁ : Δ ⊢ⁱ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊕ B , m ⟩

    ⊕R₂ : Δ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊕ B , m ⟩

    ⊕L : mayConsume Δ ⟨ A ⊕ B , m ⟩ Δ'
      →  ⟨ proj₁ Δ' , ( ⟨ A , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , k ⟩  →   ⟨ proj₁ Δ' , ⟨ B , m ⟩ ∷ proj₂ Δ' ⟩ ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    &R : Δ ⊢ⁱ ⟨ A , m ⟩ → Δ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A & B , m ⟩

    &L₁ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  ⟨ proj₁ Δ' , (⟨ A , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    &L₂ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  ⟨ proj₁ Δ' , (⟨ B , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊗R : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩ → Δ₂₃ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊗ B , m ⟩

    ⊗L : mayConsume Δ ⟨ A ⊗ B , m ⟩ Δ'
      → ⟨ proj₁ Δ' , (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊸R : ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊸ B , m ⟩

    ⊸L : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → mayConsume Δ₁₂ ⟨ A ⊸ B , m ⟩ Δ₁₂'
      → mayConsume Δ₂₃ ⟨ A ⊸ B , m ⟩ Δ₂₃'
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩
      → ⟨ proj₁ Δ₂₃ , (⟨ B , m ⟩ ∷ proj₂ Δ₂₃) ⟩ ⊢ⁱ ⟨ C , k ⟩
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
      → Δ ⊢ⁱ ⟨ ↓[ m ][ k ] A , m ⟩

    ↓L : mayConsume Δ ⟨ ↓[ m ][ k ] A , m ⟩ Δ'
      → ⟨ proj₁ Δ' , (⟨ A , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , l ⟩

    ↑R : Δ ⊢ⁱ ⟨ A , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ ↑[ m ][ k ] A , k ⟩

    ↑L : mayConsume Δ ⟨ ↑[ k ][ m ] A , k ⟩ Δ' → k ≥ l
      → ⟨ proj₁ Δ' , (⟨ A , k ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , l ⟩

    ⊤R : 
      -----------
      Δ ⊢ⁱ ⟨ ⊤ , m ⟩

    ∀L : mayConsume Δ ⟨ ∀[ A ] , m ⟩ Δ'
        → isTerm Δ t
        → ⟨ proj₁ Δ' , (⟨ (subst ∀[ A ] t) , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , k ⟩
        ----------------
        → Δ ⊢ⁱ ⟨ C , k ⟩

  {--
    Properties
  --}
  postulate
    ⊗-assoc : Δ ⊢ⁱ ⟨ A ⊗ (B ⊗ C) , m ⟩ → Δ ⊢ⁱ ⟨ (A ⊗ B) ⊗ C , m ⟩
  -- ⊗-assoc (id x x₁) = id {!  x !} {!   !}
  -- ⊗-assoc (cut x x₁ x₂ x₃ x₄ x₅ x₆ D D₁) = {!   !}
  -- ⊗-assoc (⊕L x D D₁) = {!   !}
  -- ⊗-assoc (&L₁ x D) = {!   !}
  -- ⊗-assoc (&L₂ x D) = {!   !}
  -- ⊗-assoc (⊗R x x₁ x₂ x₃ D D₁) = {!   !}
  -- ⊗-assoc (⊗L x D) = {!   !}
  -- ⊗-assoc (⊸L x x₁ x₂ x₃ x₄ x₅ x₆ x₇ D D₁) = {!   !}
  -- ⊗-assoc (𝟙L x D) = {!   !}
  -- ⊗-assoc (↓L x D) = {!   !}
  -- ⊗-assoc (↑L x x₁ D) = {!   !}
  -- ⊗-assoc (∀L x x₁ D) = {!   !}
   