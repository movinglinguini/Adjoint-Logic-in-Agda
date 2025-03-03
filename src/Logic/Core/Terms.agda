open import Data.Fin
open import Data.Nat

module Logic.Core.Terms (T : Set) where
  
  data Term : Set where
    const : T → Term
    var : ℕ → Term 