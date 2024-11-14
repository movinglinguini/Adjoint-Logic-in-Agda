open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Bool using (Bool; false; true)

open import Mode using (StructRule; _∈ᴹ_; Mode; rulesOf)

module ExplicitAdj (U : Set) (_≥_ : Mode → Mode → Set) where

  infix 10 _⊗_
  infix 10 _⊕_
  infix 10 _&_
  infix 10 _⊸_ 

  data Prop (m : Mode) : Set where
    -- An arbitrary proposition
    `_  : (A : U) → Prop m
    -- Implication
    _⊸_ : Prop m → Prop m → Prop m
    -- Tensor
    _⊗_ : Prop m → Prop m → Prop m
    -- Unit
    𝟙 : Prop m
    -- Plus - Using the binary relation rather than the n-ary version for simplicity
    _⊕_ : Prop m → Prop m → Prop m
    -- With - Using the binary version rather than the n-ary version for simplicity
    _&_ : Prop m → Prop m → Prop m
    -- Up
    Up[_]_ : ∀ { l : Mode } → (m ≥ l) → Prop l → Prop m
    -- Down
    Down[_]_ : ∀ { l : Mode } → (l ≥ m) → Prop l → Prop m

  -- Introducing the HProp as a wrapper for moded propositions to allow for lists
  -- of propositions with heterogenous modes
  data HProp : Set where
    `_ : ∀ { m : Mode } → Prop m → HProp

  private
    {-
      Defining some side functions that we'll need for our logical rules.
    -}
    _≡?_ : StructRule → StructRule → Bool
    StructRule.W ≡? StructRule.W = true
    StructRule.C ≡? StructRule.C = true
    StructRule.W ≡? StructRule.C = false
    StructRule.C ≡? StructRule.W = false 

    _∈?_ : StructRule → List StructRule → Bool
    x ∈? ∅ = false
    x ∈? (y , xs) with (x ≡? y)
    ... | true = true
    ... | false = x ∈? xs

    _∩_ : List StructRule → List StructRule → List StructRule
    ∅ ∩ _ = ∅
    _ ∩ ∅ = ∅
    (l , L) ∩ R with (l ∈? R)
    ... | true = (l , L ∩ R)
    ... | false = (L ∩ R)

  -- Helper function for extracting the mode of a proposition
  modeOf : ∀ { m : Mode } → Prop m → Mode
  modeOf { m } A = m

  -- Sigma of a list of propositions extracts the common structural rules of those propositions
  σ : List HProp → List StructRule
  σ ∅ = StructRule.W , StructRule.C , ∅
  σ (` A , As) = (rulesOf (modeOf A)) ∩ (σ As)
  
  infix 5 _⊢_

  data _≥ˡ_ : ∀ (Ψ : List HProp) (k : Mode) → Set where
    P≥k : ∀ { m : Mode } { B : Prop m } { Ψ : List HProp } { k : Mode }
      → (` B) ∈ Ψ → (modeOf (B)) ≥ k 
      ------------------------------
      → Ψ ≥ˡ k

  data _⊢_ : ∀ {m : Mode} (Ψ : List HProp) → Prop m → Set where
    id : ∀ {m : Mode} { A : Prop m }
        ------------------------------
        → (` A , ∅) ⊢ A

    cut : ∀ {m k l : Mode} { Ψ₁ Ψ₂ : List HProp } {Cₖ : Prop k} { Aₘ : Prop m }
        → Ψ₁ ≥ˡ m → m ≥ k     →   Ψ₁ ⊢ Aₘ   → (` Aₘ , Ψ₂) ⊢ Cₖ 
        -------------------------------------------------------
        → (Ψ₁ ++ Ψ₂) ⊢ Cₖ

    weaken : ∀ { m k : Mode } { Ψ : List HProp } { Cₖ : Prop k } { Aₘ : Prop m }
        → StructRule.W ∈ σ(` Aₘ , ∅)    →   Ψ ⊢ Cₖ
        ---------------------------------------------
        → (` Aₘ , Ψ) ⊢ Cₖ

    contract : ∀ { m k : Mode } { Ψ : List HProp } { Cₖ : Prop k } { Aₘ : Prop m }
        → StructRule.C ∈ σ(` Aₘ , ∅)  → ((` Aₘ) , (` Aₘ) , Ψ) ⊢ Cₖ
        -----------------------------------------------------
        → (` Aₘ , Ψ) ⊢ Cₖ
    
    ⊕R₁ : ∀ { m : Mode } { Ψ : List HProp } { Aₘ : Prop m } { Bₘ : Prop m }
        → Ψ ⊢ Aₘ
        ---------------
        → Ψ ⊢ Aₘ ⊕ Bₘ

    ⊕R₂ : ∀ { m : Mode } { Ψ : List HProp } { Aₘ : Prop m } { Bₘ : Prop m }
        → Ψ ⊢ Bₘ
        ---------------
        → Ψ ⊢ Aₘ ⊕ Bₘ
    
    ⊕L : ∀ { m k : Mode } { Ψ : List HProp } { Aₘ : Prop m } { Bₘ : Prop m } { Cₖ : Prop k }
        → (` Aₘ , Ψ) ⊢ Cₖ   →   (` Bₘ , Ψ ) ⊢ Cₖ
        -----------------------------------------
        → (` (Aₘ ⊕ Bₘ) , Ψ) ⊢ Cₖ 