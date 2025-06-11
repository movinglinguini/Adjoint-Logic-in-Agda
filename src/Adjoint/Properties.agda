open import Data.Nat
open import Data.Vec
open import Data.Product

module Adjoint.Properties 
  (Atom : Set)
  (Mode : Set)
  (mWeakenable : Mode → Set)
  (mContractable : Mode → Set)
  (mHarmless : Mode → Set)
  (_∙_⇒_ : Mode → Mode → Mode → Set)
  (_≥_ : Mode → Mode → Set) 
  where
  open import Adjoint.Core.Props Atom Mode public
  open import Adjoint.Core.Contexts 
    Atom 
    Mode  
    mWeakenable 
    mContractable 
    mHarmless 
    _∙_⇒_ 
    _≥_ 
  open import Adjoint.Core.Rules
    Atom 
    Mode  
    mWeakenable 
    mContractable 
    mHarmless 
    _∙_⇒_ 
    _≥_ 

  private
    variable
      n m : ℕ
      A : Prop
      k : Mode

  exchange-ctxt : Context (suc (n + m)) → Context (n + (suc m)) 
  exchange-ctxt {zero} Δ = Δ
  exchange-ctxt {suc n} (x ∷ x₁ ∷ Δ) = x₁ ∷ exchange-ctxt (x ∷ Δ)

  exchange-ctxt-admit : ∀ { Ψ : Context (suc (n + m)) }
    → Ψ ⊢ (A , k)
    → (exchange-ctxt { n = n } { m = m } Ψ) ⊢ (A , k) 
  exchange-ctxt-admit D = {!  !}
