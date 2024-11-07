open import Data.List using (List)

open import AgdaAdjointLogic.Mode using (Mode)

module AgdaAdjointLogic.ExplicitAdj (_≥_ : Mode → Mode → Set) where
  
  data Prop (M : Mode) : Set where
    -- An arbitrary proposition
    `_  : Mode → Prop M
    -- Implication
    _⊸_ : Prop M → Prop M → Prop M
    -- Tensor
    _⊗_ : Prop M → Prop M → Prop M
    -- Unit
    𝟙 : Prop M
    -- Plus
      --
    -- With
      -- 
    -- Up
    Up[_]_ : ∀ { L : Mode } → (M ≥ L) → Prop L → Prop M
    -- Down
    Down[_]_ : ∀ { L : Mode } → (L ≥ M) → Prop L → Prop M


    