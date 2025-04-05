open import Data.Vec
open import Data.Nat hiding (_≥_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

{-
  Generalized definition of contexts
-}
module Adjoint.Core.Contexts 
  (Atom : Set)
  (Mode : Set)
  (mWeakenable : Mode → Set)
  (mContractable : Mode → Set)
  (mHarmless : Mode → Set)
  (_∙_⇒_ : Mode → Mode → Mode → Set)
  (_≥_ : Mode → Mode → Set)
  where
  open import Adjoint.Core.Props Atom Mode

  open import CARVe.Context Prop Mode _∙_⇒_

  variable
    n : ℕ
    Δ Δ' Δ'' Δ''' Δ₁ Δ₂ Δ₃ Δ₂' Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃'  : Context n
    A B C : Prop 
    m k l m₁ m₂ : Mode

  -- A context is weakenable if all of its propositions are weakeanable
  data cWeakenable : Context n → Set where
    weak/z : cWeakenable []
    weak/s : cWeakenable Δ → mWeakenable m → cWeakenable (⟨ A , m ⟩ ∷ Δ)

  -- A context is contractable if all of its propositions are contractable
  data cContractable : Context n → Set where
    cont/z : cContractable []
    cont/s : cContractable Δ → mContractable m → cContractable (⟨ A , m ⟩ ∷ Δ)

  -- A context is exhausted if all of its propositions are "harmless".
  data cExhausted : Context n → Set where
    exh/z : cExhausted []
    exh/s : cExhausted Δ → mHarmless m → cExhausted (⟨ A , m ⟩ ∷ Δ)

  -- A context is ≥ a mode k if all of its propositions are at a mode ≥ k
  data _≥ᶜ_ : Context n → Mode → Set where
    ≥/z : [] ≥ᶜ m
    ≥/s : Δ ≥ᶜ k → m ≥ k → (⟨ A , m ⟩ ∷ Δ) ≥ᶜ k

  -- We allow optional "consumption" by optionally marking a proposition as
  -- irrelevant
  data mayConsume : Context n → Prop × Mode → Context n → Set where
    consume/yes : update Δ ⟨ A , m ⟩ ⟨ A , k ⟩ Δ' → mHarmless k
      → mayConsume Δ ⟨ A , m ⟩ Δ'

    consume/no : update Δ ⟨ A , m ⟩ ⟨ A , m ⟩ Δ → mContractable m
      → mayConsume Δ ⟨ A , m ⟩ Δ
