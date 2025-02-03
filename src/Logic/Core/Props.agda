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
    -- Plus - Using the binary relation rather than the n-ary version for simplicity
    _⊕_ : Prop → Prop → Prop
    -- With - Using the binary version rather than the n-ary version for simplicity
    _&_ : Prop → Prop → Prop
    -- Shifts
    ↑[_][_]_ : Mode → Mode → Prop → Prop
    ↓[_][_]_ : Mode → Mode → Prop → Prop
    -- for all
    ∀[_] : Prop → Prop

  variable
    A B C : Prop