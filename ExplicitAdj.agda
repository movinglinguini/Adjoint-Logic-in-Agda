open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Nullary using (¬_)
open import Data.Bool using (Bool; false; true)

open import AgdaAdjointLogic.Mode using (StructRule; _∈ᴹ_; Mode)

module AgdaAdjointLogic.ExplicitAdj (U : Set) (_≥_ : Mode → Mode → Set) where

  infix 10 _⊗_
  infix 10 _⊕_
  infix 10 _&_
  infix 10 _⊸_ 

  data Prop (M : Mode) : Set where
    -- An arbitrary proposition
    `_  : (A : U) → Prop M
    -- Implication
    _⊸_ : Prop M → Prop M → Prop M
    -- Tensor
    _⊗_ : Prop M → Prop M → Prop M
    -- Unit
    𝟙 : Prop M
    -- Plus - Using the binary relation rather than the n-ary version for simplicity
    _⊕_ : Prop M → Prop M → Prop M
    -- With - Using the binary version rather than the n-ary version for simplicity
    _&_ : Prop M → Prop M → Prop M
    -- Up
    Up[_]_ : ∀ { L : Mode } → (M ≥ L) → Prop L → Prop M
    -- Down
    Down[_]_ : ∀ { L : Mode } → (L ≥ M) → Prop L → Prop M

  private
    infix 5 _∈_
    
    _∈_ : ∀ { A : Set } ( x : A ) ( xs : List A ) → Set
    x ∈ xs = Any (x ≡_) xs

    _∉_ : ∀ { A : Set } ( x : A ) ( xs : List A ) → Set
    x ∉ xs  = ¬ (x ∈ xs)

    _∩_ : ∀ { A : Set } (L : List A) (R : List A) → List A
    ∅ ∩ _ = ∅
    _ ∩ ∅ = ∅
    (l , L) ∩ R with l ∈ R
    ... | yes = (l , L ∩ R)
    -- This clause is unreachable for some reason :(
    (l , L) ∩ R with l ∉ R
    ... | yes = L ∩ R
    

  
  infix 5 _⊢_

  data _⊢_ : ∀ {M L : Mode} (Ψ : List (Prop L)) → Prop M → Set where
    id : ∀ {m : Mode} { A : Prop m }
        ------------------------------
        → (A , ∅) ⊢ A

    cut : ∀ {m k l : Mode} { Ψ₁ Ψ₂ : List (Prop l) } {Cₖ : Prop k}
        -------------------------------------------
        → (Ψ₁ ++ Ψ₂) ⊢ Cₖ
    

      