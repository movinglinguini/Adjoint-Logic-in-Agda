open import Data.Product

module Adjoint.Core.Props 
  (Atom : Set) 
  (Mode : Set)
  (_≥_ : Mode → Mode → Set)
  where
  
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
    -- Upshift
    ↑[_]_ : ∀ { m k } → m ≥ k → Prop → Prop
    -- Downshift
    ↓[_]_ : ∀ { m k } → m ≥ k → Prop → Prop
  
  ModedProp = Prop × Mode
