open import Data.Fin
open import Data.Nat

module Logic.Core.Terms (T : Set) where
  
  data Term : Set where
    const : T → Term
    var : ∀ {n : ℕ}→ (m : Fin n) → Term 