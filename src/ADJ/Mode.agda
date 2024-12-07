open import Data.List using (List; _++_; any) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.List.Relation.Binary.Sublist.Setoid using (_⊇_)
open import Relation.Binary.Core using (Rel)

module ADJ.Mode where

  data StructRule : Set where
    W : StructRule
    C : StructRule

  record Mode : Set where
    field
      structRules : List StructRule

  rulesOf : Mode → List StructRule
  rulesOf record { structRules = structRules } = structRules

  -- some example modes
  private
    Linear : Mode
    Linear = record { structRules = ∅ }

    Unrestricted : Mode
    Unrestricted = record { structRules = StructRule.W , StructRule.C , ∅ }

  open Data.List public renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)




 