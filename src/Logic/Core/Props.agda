open import Data.Nat
open import Logic.Core.Modes

module Logic.Core.Props (Atom : Set) where

  infix 50 _⊗_
  infix 60 `_
  
  data Prop : Set where
    -- An arbitrary proposition
    `_  : (A : Atom) → Prop
    -- Implication
    _⊸_ : Prop → Prop → Prop
    -- Tensor
    _⊗_ : Prop → Prop → Prop
    -- Unit
    𝟙 : Prop
    -- Top
    ⊤ : Prop
    -- for all
    ∀[_][_] : ℕ → Prop → Prop

  variable
    A B C : Prop