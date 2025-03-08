open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Nat hiding (_≥_)

open import Logic.Core.Props
open import Logic.Core.Terms

module Logic.Adjoint 
  (PropAtom : Set) 
  (TermAtom : Set) 
  (subst-PropAtom : PropAtom → Term TermAtom 0 → PropAtom)  where

  open import Logic.Core.Modes
  open import Logic.Core.Contexts PropAtom TermAtom

  private
    -- Helper for the substitution function
    subst-One : Prop (PropAtom) → Term (TermAtom) 0 → Prop (PropAtom)
    subst-One (` A) t = ` (subst-PropAtom A t)
    subst-One (L ⊸ R) t = subst-One L t ⊸ subst-One R t
    subst-One (L ⊗ R) t = (subst-One L t) ⊗ (subst-One R t)
    subst-One 𝟙 t = 𝟙
    subst-One ⊤ t = ⊤
    subst-One ∀[ zero ][ A ] t = subst-One A t
    subst-One ∀[ suc n ][ A ] t = ∀[ n ][ subst-One A t ]

  {--------------------
    Substitution function
  ---------------------}
  subst : ∀ { n } → Prop (PropAtom) → Vec (Term TermAtom 0) n → Prop (PropAtom)
  subst A [] = A
  subst A (t ∷ ts) = subst (subst-One A t) ts

  private
    variable
      x y n : ℕ 
      Δ Δ' Δ₁ Δ₁' Δ₂ Δ₂' Δ₃ Δ₃' Δ₁₂ Δ₁₂' Δ₂₃ Δ₂₃' : Context x y
      m k l : Mode
      t : Term TermAtom 0
      ts : Vec (Term TermAtom 0) n

  data _⊢ⁱ_ : Context x y → (Prop (PropAtom) × Mode) → Set where

    id : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ' → cWeakenable Δ'
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A , m ⟩

    ⊗R : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩ → Δ₂₃ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊗ B , m ⟩

    ⊗L : mayConsume Δ ⟨ A ⊗ B , m ⟩ Δ'
      → ⟨ proj₁ Δ' , (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

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

    ⊤R : 
      -----------
      Δ ⊢ⁱ ⟨ ⊤ , m ⟩

    ∀L : ∀ { n } ( ts : Vec (Term (TermAtom) 0) (suc n)) 
        → mayConsume Δ ⟨ ∀[ n ][ A ] , m ⟩ Δ'
        → areTerms Δ ts
        → ⟨ proj₁ Δ' , (⟨ (subst ∀[ n ][ A ] ts) , m ⟩ ∷ proj₂ Δ') ⟩ ⊢ⁱ ⟨ C , k ⟩
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
   