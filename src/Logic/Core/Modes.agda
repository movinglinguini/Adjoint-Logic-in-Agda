open import Data.Bool
open import Data.Vec
open import Data.Nat hiding (_≥_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module Logic.Core.Modes where

  data Mode : Set where
    Linear : Mode
    Unrestricted : Mode
    Irrelevant : Mode

  variable
    m k l q m' m₁ m₂ m₃ m₂' m₁₂ m₂₃ : Mode

  data mWeakenable : Mode → Set where
    mweak/u : mWeakenable Unrestricted
    mweak/i : mWeakenable Irrelevant

  data mContractable : Mode → Set where
    mcontract/u : mContractable Unrestricted
    mcontract/i : mContractable Irrelevant

  data harmless : Mode → Set where
    harmless/u : harmless Unrestricted
    harmless/i : harmless Irrelevant

  data _≥_ : Mode → Mode → Set where
    u≥m : Unrestricted ≥ m
    l≥l : Linear ≥ Linear
    i≥m : Irrelevant ≥ m

  data _∙_⇒_ : Mode → Mode → Mode → Set where
    u∙u : Unrestricted ∙ Unrestricted ⇒ Unrestricted
    i∙i : Irrelevant ∙ Irrelevant ⇒ Irrelevant
    i∙l : Irrelevant ∙ Linear ⇒ Linear
    l∙i : Linear ∙ Irrelevant ⇒ Linear

  ----------------------------------------------------------
  -- ≥ is a preorder
  ----------------------------------------------------------

  ≥-refl : m ≥ m
  ≥-refl { Unrestricted } = u≥m
  ≥-refl { Linear } = l≥l
  ≥-refl { Irrelevant } = i≥m

  ≥-trans : m₁ ≥ m₂ → m₂ ≥ m₃ → m₁ ≥ m₃
  ≥-trans u≥m u≥m = u≥m
  ≥-trans u≥m l≥l = u≥m
  ≥-trans u≥m i≥m = u≥m
  ≥-trans l≥l l≥l = l≥l
  ≥-trans i≥m u≥m = i≥m
  ≥-trans i≥m l≥l = i≥m
  ≥-trans i≥m i≥m = i≥m

  ----------------------------------------------------------
  -- Properties of •
  ----------------------------------------------------------

  ∙-comm : m₁ ∙ m₂ ⇒ m → m₂ ∙ m₁ ⇒ m
  ∙-comm u∙u = u∙u
  ∙-comm i∙i = i∙i
  ∙-comm i∙l = l∙i
  ∙-comm l∙i = i∙l

  ∙-func : m₁ ∙ m₂ ⇒ m → m₁ ∙ m₂ ⇒ m' → m ≡ m'
  ∙-func u∙u u∙u = refl
  ∙-func i∙i i∙i = refl
  ∙-func i∙l i∙l = refl
  ∙-func l∙i l∙i = refl

  ∙-irrel-is-id : m₁ ∙ Irrelevant ⇒ m₂ → m₁ ≡ m₂
  ∙-irrel-is-id i∙i = refl
  ∙-irrel-is-id l∙i = refl

  data ∙GetId : Mode → Set where
    ∙/getid : m ∙ m' ⇒ m → harmless m' → ∙GetId m

  ∙-getid : ∀ ( m : Mode ) → ∙GetId m
  ∙-getid Linear = ∙/getid l∙i harmless/i
  ∙-getid Unrestricted = ∙/getid u∙u harmless/u
  ∙-getid Irrelevant = ∙/getid i∙i harmless/i

  data ∙assoc : m₁ ∙ m₂ ⇒ m₁₂ → m₁₂ ∙ m₃ ⇒ m → Set where
    ∙/assoc : {D1 : m₁ ∙ m₂ ⇒ m₁₂} {D2 : m₁₂ ∙ m₃ ⇒ m}
      → m₁ ∙ m₂₃ ⇒ m → m₂ ∙ m₃ ⇒ m₂₃ → ∙assoc D1 D2

  ∙-assoc : (D1 : m₁ ∙ m₂ ⇒ m₁₂) (D2 : m₁₂ ∙ m₃ ⇒ m) → ∙assoc D1 D2
  ∙-assoc u∙u u∙u = ∙/assoc u∙u u∙u
  ∙-assoc i∙i i∙i = ∙/assoc i∙i i∙i
  ∙-assoc i∙i i∙l = ∙/assoc i∙l i∙l
  ∙-assoc i∙l l∙i = ∙/assoc i∙l l∙i
  ∙-assoc l∙i l∙i = ∙/assoc l∙i i∙i

  •-cancl : m₁ ∙ m₂ ⇒ m → m₁ ∙ m₂' ⇒ m → m₂ ≡ m₂'
  •-cancl u∙u u∙u = refl
  •-cancl i∙i i∙i = refl
  •-cancl i∙l i∙l = refl
  •-cancl l∙i l∙i = refl

  ----------------------------------------------------------
  -- Properties of mode predicates
  ----------------------------------------------------------

  harmless_to_mWeakenable : harmless m → mWeakenable m
  harmless_to_mWeakenable harmless/u = mweak/u
  harmless_to_mWeakenable harmless/i = mweak/i

  harmless_to_mContractable : harmless m → mContractable m
  harmless_to_mContractable harmless/u = mcontract/u
  harmless_to_mContractable harmless/i = mcontract/i  