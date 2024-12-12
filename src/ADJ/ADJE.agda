open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)

open import ADJ.Mode using (StructRule; Mode; rulesOf)

module ADJ.ADJE (U : Set) (BotMode : Mode) (_≥_ : Mode → Mode → Set) (_≥?_ : (m k : Mode)  → Dec (m ≥ k)) where

  infix 10 _⊗_
  infix 10 _⊕_
  infix 10 _&_
  infix 10 _⊸_
  infix 10 𝟙
  

  data Prop (m : Mode) : Set where
    -- An arbitrary proposition
    `_  : (A : U) → Prop m
    -- Implication
    _⊸_ : Prop m → Prop m → Prop m
    -- Tensor
    _⊗_ : Prop m → Prop m → Prop m
    -- Unit
    𝟙 : Prop m
    -- Top
    ⊤ : Prop m
    -- Plus - Using the binary relation rather than the n-ary version for simplicity
    _⊕_ : Prop m → Prop m → Prop m
    -- With - Using the binary version rather than the n-ary version for simplicity
    _&_ : Prop m → Prop m → Prop m
    -- Up from l
    Up[_]_ : ∀ { l : Mode } → (m ≥ l) → Prop l → Prop m
    -- Down from l
    Down[_]_ : ∀ { l : Mode } → (l ≥ m) → Prop l → Prop m
    -- For all
    all_ : Prop m → Prop m

  private
    -- Example propositions
    Linear : Mode
    Linear = record { structRules = ∅ }

    Unrestricted : Mode
    Unrestricted  = record { structRules = ∅ }

    postulate
      A : U
      B : U

      U≥L : Unrestricted ≥ Linear

    Aₗ : Prop Linear
    Aₗ = ` A
    Bₗ : Prop Linear
    Bₗ = ` B

    LinearProp : Prop Linear
    LinearProp = Aₗ ⊸ Bₗ

    UnrestrictedProp : Prop Unrestricted
    UnrestrictedProp = Up[ U≥L ] LinearProp

    DownshiftedProp : Prop Linear
    DownshiftedProp = Down[ U≥L ] UnrestrictedProp

  -- Introducing the HProp as a wrapper for moded propositions to allow for lists
  -- of propositions with heterogenous modes
  data HProp : Set where
    `_ : ∀ { m : Mode } → Prop m → HProp

  toHProps : ∀ { m } → List (Prop m) → List (HProp)
  toHProps ∅ = ∅
  toHProps (x , xs) = ` x ,  (toHProps xs)

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

  leastModeOf : List HProp → Mode → Mode
  leastModeOf ∅ m = m
  leastModeOf (` A , Ψ) m with modeOf A ≥? m
  ... | yes _ = leastModeOf Ψ m
  ... | no _ = leastModeOf Ψ (modeOf A)
    
  -- Definition for comparing a mode to all modes of a list of propositions

  data _≥ˡ_ : ∀ (Ψ : List HProp) (k : Mode) → Set where
    ∅≥k : ∀ { k : Mode }
        ---------------------
        → ∅ ≥ˡ k

    P≥k : ∀ { m : Mode } { B : Prop m } { Ψ : List HProp } { k : Mode }
        → (leastModeOf Ψ BotMode) ≥ k 
        ------------------------------
        → Ψ ≥ˡ k

  {-
    Finally, the rules
  -}
  data _⊢_ : ∀ {m : Mode} (Ψ : List HProp) → Prop m → Set where
    {- Axiom -}
    id : ∀ {m : Mode} { A : Prop m }
        ------------------------------
        → (` A , ∅) ⊢ A

    {- Cut -}
    cut : ∀ {m k l : Mode} { Ψ₁ Ψ₂ : List HProp } {Cₖ : Prop k} { Aₘ : Prop m }
        → Ψ₁ ≥ˡ m → m ≥ k     →   Ψ₁ ⊢ Aₘ   → (` Aₘ , Ψ₂) ⊢ Cₖ 
        -------------------------------------------------------
        → (Ψ₁ ++ Ψ₂) ⊢ Cₖ

    {- Structural Rules -}
    weaken : ∀ { m k : Mode } { Ψ : List HProp } { Cₖ : Prop k } { Aₘ : Prop m }
        → StructRule.W ∈ (rulesOf m)    →   Ψ ⊢ Cₖ
        ---------------------------------------------
        → (` Aₘ , Ψ) ⊢ Cₖ

    contract : ∀ { m k : Mode } { Ψ : List HProp } { Cₖ : Prop k } { Aₘ : Prop m }
        → StructRule.C ∈ (rulesOf m)  → ((` Aₘ) , (` Aₘ) , Ψ) ⊢ Cₖ
        -----------------------------------------------------------
        → (` Aₘ , Ψ) ⊢ Cₖ

    -- Exchange isn't included in the ADJ paper, and instead is left as implicitly admitted.
    -- Writing it in the style of Abramsky's Computational interpretations of linear logic, where we are
    -- exchanging propositions. This is in contrast to Wen Kokke's model of intuitionistic logic, where
    -- she exchanges whole pieces of context.
    exchange : ∀ { m k l : Mode } { Ψ₁ Ψ₂ : List HProp } { Aₘ : Prop m } { Bₗ : Prop l } { Cₖ : Prop k }
        → ((Ψ₁ ,′ (` Aₘ)) ++ ((` Bₗ) , Ψ₂)) ⊢ Cₖ
        ------------------------------------
        → ((Ψ₁ ,′ (` Bₗ)) ++ ((` Aₘ) , Ψ₂)) ⊢ Cₖ
    
    -- Oplus
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

    -- With
    &R : ∀ { m : Mode } { Ψ : List HProp } { Aₘ Bₘ : Prop m }
        → Ψ ⊢ Aₘ    →   Ψ ⊢ Bₘ
        ------------------------
        → Ψ ⊢ Aₘ & Bₘ

    &L₁ : ∀ { m k : Mode } { Ψ : List HProp } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → (` Aₘ , Ψ) ⊢ Cₖ
        --------------
        → (` (Aₘ & Bₘ) , Ψ) ⊢ Cₖ

    &L₂ : ∀ { m k : Mode } { Ψ : List HProp } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → (` Bₘ , Ψ) ⊢ Cₖ
        --------------
        → (` (Aₘ & Bₘ) , Ψ) ⊢ Cₖ 
    -- Tensor
    ⊗R : ∀ { m : Mode } { Ψ₁ Ψ₂ : List HProp } { Aₘ Bₘ : Prop m }
        → Ψ₁ ⊢ Aₘ   →   Ψ₂ ⊢ Bₘ
        -------------------------
        → (Ψ₁ ++ Ψ₂) ⊢ Aₘ ⊗ Bₘ

    ⊗L : ∀ { m k : Mode } { Ψ : List HProp } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → (` Aₘ , ` Bₘ , Ψ) ⊢ Cₖ
        --------------------------
        → (` (Aₘ ⊗ Bₘ) , Ψ) ⊢ Cₖ
    -- Lolli
    ⊸R : ∀ { m : Mode } { Ψ : List HProp } { Aₘ Bₘ : Prop m }
        → (` Aₘ , Ψ) ⊢ Bₘ
        --------------------
        → Ψ ⊢ Aₘ ⊸ Bₘ

    ⊸L : ∀ { m k : Mode } { Ψ₁ Ψ₂ : List HProp } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → Ψ₁ ⊢ Aₘ   →   (` Bₘ , Ψ₂) ⊢ Cₖ
        ----------------------------------
        → (` (Aₘ ⊸ Bₘ) , (Ψ₁ ++ Ψ₂)) ⊢ Cₖ

    -- Top - no left rule for top
    ⊤R : ∀ { m : Mode } { Ψ : List HProp }
        ------------------
        → Ψ ⊢ ⊤ { m } 

    -- Multiplicative unit
    𝟙R : ∀ { m : Mode } { Ψ : List HProp }
        → StructRule.W ∈ σ(Ψ)
        -----------------------
        → Ψ ⊢ 𝟙 {m}

    𝟙L : ∀ { m k : Mode } { Ψ : List HProp } { Cₖ : Prop k }
        → Ψ ⊢ Cₖ
        ----------
        → ((` (𝟙 {m})) , Ψ) ⊢ Cₖ 

    -- Down shift
    DownR : ∀ { m k : Mode } { Ψ : List HProp } { Aₘ : Prop m } { m≥k : m ≥ k }
        → Ψ ≥ˡ m    →   Ψ ⊢ Aₘ
        -----------------------
        → Ψ ⊢ Down[ m≥k ] Aₘ
    
    DownL : ∀ { m l k : Mode } { Ψ : List HProp } { Aₘ : Prop m } { Cₗ : Prop l } { m≥k : m ≥ k }
        → (` Aₘ , Ψ) ⊢ Cₗ 
        ------------------
        → (` Down[ m≥k ] Aₘ , Ψ) ⊢ Cₗ
    -- Up shift
    UpR : ∀ { m k : Mode } { Ψ : List HProp } { Aₖ : Prop k } { m≥k : m ≥ k }
        → Ψ ⊢ Aₖ
        -----------
        → Ψ ⊢ Up[ m≥k ] Aₖ

    UpL : ∀ { m k l : Mode } { Ψ : List HProp } { Aₖ : Prop k } { Cₗ : Prop l } { m≥k : m ≥ k }
        → k ≥ l         →       (` Aₖ , Ψ) ⊢ Cₗ
        ----------------------------------------
        → (` Up[ m≥k ] Aₖ , Ψ) ⊢ Cₗ 

    -- For all rules taken from Frank Pfenning's notes on sequent calculus: https://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf
    -- Note: Not too sure on allR
    allR : ∀ { m : Mode } { Ψ : List HProp } { Aₘ : Prop m }
        → (substitution : Prop m → Prop m)
        → Ψ ⊢ substitution Aₘ
        -----------------
        → Ψ ⊢ all Aₘ

    allL : ∀ { m k : Mode } { Ψ : List HProp } { Aₘ : Prop m } { Cₖ : Prop k }
        → (substitution : Prop m → Prop m)
        → (` (substitution Aₘ) , Ψ) ⊢ Cₖ
        --------------------------
        → (` all Aₘ , Ψ) ⊢ Cₖ

    -- TODO: show local soundness and completeness of top and all