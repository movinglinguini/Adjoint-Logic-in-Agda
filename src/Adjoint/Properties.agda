open import Data.Nat
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
  {- Repackage all the parts -}
  open import Adjoint.Core.Props Atom Mode
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
      n : ℕ
      A B : Prop
      m : Mode
      Ψ : Context n
