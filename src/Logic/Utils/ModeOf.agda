open import Data.Product renaming (_,_ to ⟨_,_⟩)

module Logic.Utils.ModeOf (Atom : Set) where
  open import Logic.Core.Props Atom
  open import Logic.Core.Modes

  modeOf : (Prop × Mode) → Mode
  modeOf ⟨ p , m ⟩ = m 

