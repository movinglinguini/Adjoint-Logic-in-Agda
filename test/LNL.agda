open import Data.String
{-
  Here, we instantiate Adjoint Logic to have just unrestricted
  and linear propositions.
-}
module LNL where
  {-
    Setup. To set up this instance of Adjoint Logic, we will need...
  -}
  -- ...our modes...
  data Mode : Set where
    Linear : Mode
    Unrestricted : Mode
    Irrelevant : Mode

  -- ... a binary operation on modes...
  data _∙_⇒_ : Mode → Mode → Mode → Set where
    u∙u : Unrestricted ∙ Unrestricted ⇒ Unrestricted
    i∙i : Irrelevant ∙ Irrelevant ⇒ Irrelevant
    i∙l : Irrelevant ∙ Linear ⇒ Irrelevant
    l∙i : Linear ∙ Irrelevant ⇒ Irrelevant

  -- ...a preorder on our modes...
  data _≥_ : Mode → Mode → Set where
    u≥m : ∀ { m } → Unrestricted ≥ m
    i≥m : ∀ { m } → Irrelevant ≥ m
    m≥l : ∀ { m } → m ≥ Linear

  -- ...structural rules for our modes...
  data mWeakenable : Mode → Set where
    weak/unr : mWeakenable Unrestricted
    weak/irr : mWeakenable Irrelevant
  
  data mContractable : Mode → Set where
    cont/unr : mContractable Unrestricted
    cont/irr : mContractable Irrelevant
  
  data mHarmless : Mode → Set where
    harml/unr : mHarmless Unrestricted
    harml/irr : mHarmless Irrelevant

  PropAtom = String

  -- Instantiate Adjoint Logic
  open import Adjoint.Logic
    PropAtom
    Mode
    mWeakenable
    mContractable
    mHarmless
    _∙_⇒_
    _≥_


  
  
  
