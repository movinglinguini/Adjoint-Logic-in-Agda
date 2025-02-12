open import Data.Fin
open import Data.Nat

module Logic.Core.Terms (T : Set) where
  
  data Term : Set where
    term : T → Term
    var : ℕ → Term

  variable
    x x₁ x₂ t t₁ t₂ : Term 