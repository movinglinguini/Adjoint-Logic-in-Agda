open import Data.Nat hiding (_≥_; _≥?_)
open import Data.String hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊇_)
open import Relation.Binary.Definitions using (DecidableEquality)

open import ADJ.Mode

module Test where

  data Term : Set where
    true : Term
    false : Term
    #_ : ℕ → Term
  
  data Atom : Set where
    v : Atom
    v[_] : Term → Atom

  ModeLin : Mode
  ModeLin = record { structRules = ∅ }

  ModeUnr : Mode
  ModeUnr = record { structRules = (StructRule.W , StructRule.C , ∅) }

  private
    _≟S_ : DecidableEquality StructRule
    StructRule.W ≟S StructRule.W = yes refl
    StructRule.W ≟S StructRule.C = no λ()
    StructRule.C ≟S StructRule.W = no λ()
    StructRule.C ≟S StructRule.C = yes refl

  open import Data.List.Relation.Binary.Sublist.DecPropositional _≟S_ using (_⊆?_)

  -- Our preorder on modes
  _≥_ : Mode → Mode → Set
  m ≥ k = Mode.structRules m ⊇ Mode.structRules k

  -- Decidable preorder on modes
  _≥?_ : ∀ (m k : Mode)  → Dec (m ≥ k)
  m ≥? k with Mode.structRules k ⊆? Mode.structRules m
  ... | yes k⊆m = yes k⊆m
  ... | no ¬k⊆m = no  ¬k⊆m

  open import ADJ.ADJE Atom Term ModeLin _≥_ _≥?_

  -- Test propositon

  subst : ∀ { m } → Term → Prop m → Prop m
  subst t (` v) = ` v
  subst t (` v[ true ]) = ` v[ true ]
  subst t (` v[ false ]) = ` v[ false ]
  subst t (` v[ # x ]) with x
  ... | zero = ` v[ t ]
  ... | suc x = ` v[ # x ]
  subst t (P ⊸ P₁) = (subst t P) ⊸ (subst t P₁)
  subst t (P ⊗ P₁) = (subst t P) ⊗ (subst t P₁)
  subst t 𝟙 = 𝟙
  subst t ⊤ = ⊤
  subst t (P ⊕ P₁) = (subst t P) ⊕ (subst t P₁)
  subst t (P & P₁) = (subst t P) & (subst t P₁)
  subst t (Up[ x ] P) = Up[ x ] (subst t P)
  subst t (Down[ x ] P) = Down[ x ] (subst t P)
  subst t ∀[ P ] = ∀[ subst t P ]

  PropA : Prop ModeLin
  PropA = ∀[ ` v[ # 0 ] ⊸ ` v[ false ] ]

  PropB : Prop ModeLin
  PropB = ` v[ true ]

  PropC : Prop ModeLin
  PropC = ` v[ false ]
 
  _ : ((∅ , PropB) , PropA) ⊢ PropC
  _ = ∀L₁ subst true (⊸L {_} {_} {∅ , PropB} {∅} id id)
  