open import Data.List using (List; _++_; any) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Relation.Binary.PropositionalEquality using (_≡_)

module AgdaAdjointLogic.Mode where

  data StructRule : Set where
    W : StructRule
    C : StructRule

  infix 15 `_

  data Mode : Set where
    `_ : List StructRule → Mode
  
  infix 10 _∈ᴹ_
  data _∈ᴹ_ : ∀ (S : StructRule) (M : Mode) → Set where 
    id : ∀ { R S } 
        -----------------
        → R ∈ᴹ `( R , S )

    search : ∀ { R Q S } 
        → R ∈ᴹ  ` S
        -------------
        → R ∈ᴹ `(Q , S)


  data _≥_ : ∀ (m k : Mode) → Set where
    refl : ∀ { m }
        --------------
        → m ≥ m
    
    trans : ∀ { l m n }
        → l ≥ m → m ≥ n
          -----------------
        → l ≥ n

  rulesOf : Mode → List StructRule
  rulesOf (` L) = L

  