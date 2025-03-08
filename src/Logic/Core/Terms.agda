open import Data.Fin
open import Data.Nat

module Logic.Core.Terms (TermAtom : Set) where
  
  -- A term is either a constant or a scoped variable.
  data Term : ℕ → Set where
    const : ∀ { n } → TermAtom → Term n
    var : ∀ { n } ( m : Fin n ) → Term n