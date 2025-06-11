open import Data.Vec
open import Data.Nat hiding (_≥_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

{-
  Generalized definition of contexts
-}
module Adjoint.Core.Contexts 
  (Atom : Set)
  (Mode : Set)
  (mWeakenable : Mode → Set)
  (mContractable : Mode → Set)
  (mHarmless : Mode → Set)
  (_∙_⇒_ : Mode → Mode → Mode → Set)
  (_≥_ : Mode → Mode → Set)
  where
  open import Adjoint.Core.Props Atom Mode _≥_

  open import CARVe.Context Prop Mode _∙_⇒_ public
  private 
    variable
      n q : ℕ
      Δ Δ' Δ'' Δ''' Δ₁ Δ₂ Δ₃ Δ₄ Δ₅ Δ₆ Δ₂' Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃'  : Context n
      A B C : Prop 
      m k l m₁ m₂ : Mode

  -- A context is weakenable if all of its propositions are weakeanable
  data cWeakenable : Context n → Set where
    weak/z : cWeakenable []
    weak/s : cWeakenable Δ → mWeakenable m → cWeakenable (⟨ A , m ⟩ ∷ Δ)

  -- A context is contractable if all of its propositions are contractable
  data cContractable : Context n → Set where
    cont/z : cContractable []
    cont/s : cContractable Δ → mContractable m → cContractable (⟨ A , m ⟩ ∷ Δ)

  -- A context is exhausted if all of its propositions are "harmless".
  data cExhausted : Context n → Set where
    exh/z : cExhausted []
    exh/s : cExhausted Δ → mHarmless m → cExhausted (⟨ A , m ⟩ ∷ Δ)

  -- A context is ≥ a mode k if all of its propositions are at a mode ≥ k
  data _≥ᶜ_ : Context n → Mode → Set where
    ≥/z : [] ≥ᶜ m
    ≥/s : Δ ≥ᶜ k → m ≥ k → (⟨ A , m ⟩ ∷ Δ) ≥ᶜ k

  -- We allow optional "consumption" by optionally marking a proposition as
  -- irrelevant
  data mayConsume : Context n → Prop × Mode → Context q → Set where
    consume/yes :
      update Δ ⟨ A , m ⟩ ⟨ A , k ⟩ Δ' → mHarmless k 
      → mayConsume Δ ⟨ A , m ⟩ Δ'

    consume/no : 
      update Δ ⟨ A , m ⟩ ⟨ A , m ⟩ Δ
      → mayConsume Δ ⟨ A , m ⟩ Δ


  {- Properties of concatenated contexts -}

  -- If we can merge two pairs of contexts, the concatenation of those pairs is also
  -- mergeable.
  merge-concat : merge Δ₁ Δ₂ Δ₃ → merge Δ₄ Δ₅ Δ₆ → merge (Δ₁ ++ Δ₄) (Δ₂ ++ Δ₅) (Δ₃ ++ Δ₆)
  merge-concat merge/z merge/z = merge/z
  merge-concat merge/z (merge/s M2 x) = merge/s M2 x
  merge-concat (merge/s M1 x) merge/z = merge/s (merge-concat M1 merge/z) x
  merge-concat (merge/s M1 x) (merge/s M2 x₁) = merge/s (merge-concat M1 (merge/s M2 x₁)) x 

  weak-concat : cWeakenable Δ₁ → cWeakenable Δ₂ → cWeakenable (Δ₁ ++ Δ₂)
  weak-concat weak/z weak/z = weak/z
  weak-concat weak/z (weak/s Δ₂-weak x) = weak/s Δ₂-weak x
  weak-concat (weak/s Δ₁-weak x) Δ₂-weak = weak/s (weak-concat Δ₁-weak Δ₂-weak) x

  {- Properties of the ≥ᶜ -}
  ≥ᶜ-concat : Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → (Δ₁ ++ Δ₂) ≥ᶜ m
  ≥ᶜ-concat ≥/z ≥/z = ≥/z
  ≥ᶜ-concat ≥/z (≥/s in2 x) = ≥/s in2 x
  ≥ᶜ-concat (≥/s in1 x) ≥/z = ≥/s (≥ᶜ-concat in1 ≥/z) x
  ≥ᶜ-concat (≥/s in1 x) (≥/s in2 x₁) = ≥/s (≥ᶜ-concat in1 (≥/s in2 x₁)) x