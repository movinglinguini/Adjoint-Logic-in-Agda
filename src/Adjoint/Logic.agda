open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Adjoint.Logic   
  (Atom : Set)
  (Mode : Set)
  (mWeakenable : Mode → Set)
  (mContractable : Mode → Set)
  (mHarmless : Mode → Set)
  (_∙_⇒_ : Mode → Mode → Mode → Set)
  (_≥_ : Mode → Mode → Set) 
  where

  {- Repackage all the parts -}
  open import Adjoint.Core.Props Atom Mode _≥_ public
  open import Adjoint.Core.Contexts 
    Atom 
    Mode  
    mWeakenable 
    mContractable 
    mHarmless 
    _∙_⇒_ 
    _≥_ 
    public
  open import Adjoint.Core.Rules 
    Atom 
    Mode  
    mWeakenable 
    mContractable 
    mHarmless 
    _∙_⇒_ 
    _≥_ 
    public