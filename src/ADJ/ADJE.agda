open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.List using (List) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)

open import ADJ.Mode using (StructRule; Mode; rulesOf)

module ADJ.ADJE (Atoms : Set) (Terms : Set) (BotMode : Mode) (_≥_ : Mode → Mode → Set) (_≥?_ : (m k : Mode)  → Dec (m ≥ k)) where
  
  infix 30 `_
  infix 20 _⊗_
  infix 10 _⊕_
  infix 10 _&_
  infix 10 _⊸_
  infix 10 𝟙
  

  data Prop (m : Mode) : Set where
    -- An arbitrary proposition
    `_  : (A : Atoms) → Prop m
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
    ∀[_] : Prop m → Prop m

  private
    -- Example propositions
    Linear : Mode
    Linear = record { structRules = ∅ }

    Unrestricted : Mode
    Unrestricted  = record { structRules = ∅ }

    postulate
      A : Atoms
      B : Atoms

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
  
  infixr 5 _,_
  data Context : Set where
    ∅ : Context
    _,_ : ∀ { m } → Context → Prop m → Context

  -- Concatenating contexts
  _++_ : Context → Context → Context
  ∅ ++ R = R
  (L , x) ++ R = L ++ (R , x)

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
  σ : Context → List StructRule
  σ ∅ = StructRule.W , StructRule.C , ∅
  σ (As , A) = (rulesOf (modeOf A)) ∩ (σ As)
  
  infix 5 _⊢_

  leastModeOf : Context → Mode → Mode
  leastModeOf ∅ m = m
  leastModeOf (Ψ , A) m with modeOf A ≥? m
  ... | yes _ = leastModeOf Ψ m
  ... | no _ = leastModeOf Ψ (modeOf A)
    
  -- Definition for comparing a mode to all modes of a list of propositions

  data _≥ˡ_ : ∀ (Ψ : Context) (k : Mode) → Set where
    ∅≥k : ∀ { k : Mode }
        ---------------------
        → ∅ ≥ˡ k

    P≥k : ∀ { m : Mode } { B : Prop m } { Ψ : Context } { k : Mode }
      → (leastModeOf Ψ BotMode) ≥ k 
      ------------------------------
      → Ψ ≥ˡ k

  {-
    Finally, the rules
  -}
  data _⊢_ : ∀ {m : Mode} (Ψ : Context) → Prop m → Set where
    {- Axiom -}
    id : ∀ {m : Mode} { A : Prop m }
        ------------------------------
        → (∅ , A) ⊢ A

    {- Cut -}
    cut : ∀ {m k l : Mode} { Ψ₁ Ψ₂ : Context } {Cₖ : Prop k} { Aₘ : Prop m }
        → Ψ₁ ≥ˡ m → m ≥ k     →   Ψ₁ ⊢ Aₘ   → (Ψ₂ , Aₘ) ⊢ Cₖ 
        -------------------------------------------------------
        → (Ψ₁ ++ Ψ₂) ⊢ Cₖ

    {- Structural Rules -}
    weaken : ∀ { m k : Mode } { Ψ : Context } { Cₖ : Prop k } { Aₘ : Prop m }
        → StructRule.W ∈ (rulesOf m)    →   Ψ ⊢ Cₖ
        ---------------------------------------------
        → (Ψ , Aₘ) ⊢ Cₖ

    contract : ∀ { m k : Mode } { Ψ : Context } { Cₖ : Prop k } { Aₘ : Prop m }
        → StructRule.C ∈ (rulesOf m)  → ((Ψ , Aₘ) , Aₘ) ⊢ Cₖ
        -----------------------------------------------------------
        → (Ψ , Aₘ) ⊢ Cₖ

    -- Exchange isn't included in the ADJ paper, and instead is left as implicitly admitted.
    -- Writing it in the style of Abramsky's Computational interpretations of linear logic, where we are
    -- exchanging propositions. This is in contrast to Wen Kokke's model of intuitionistic logic, where
    -- she exchanges whole pieces of context.
    exchange : ∀ { m k l : Mode } { Ψ₁ Ψ₂ : Context } { Aₘ : Prop m } { Bₗ : Prop l } { Cₖ : Prop k }
        → ((Ψ₁ , Aₘ) ++ (Ψ₂ , Bₗ)) ⊢ Cₖ
        ------------------------------------
        → ((Ψ₁ ,  Bₗ) ++ (Ψ₂ , Aₘ)) ⊢ Cₖ
    
    -- -- Oplus
    ⊕R₁ : ∀ { m : Mode } { Ψ : Context } { Aₘ : Prop m } { Bₘ : Prop m }
        → Ψ ⊢ Aₘ
        ---------------
        → Ψ ⊢ Aₘ ⊕ Bₘ

    ⊕R₂ : ∀ { m : Mode } { Ψ : Context } { Aₘ : Prop m } { Bₘ : Prop m }
        → Ψ ⊢ Bₘ
        ---------------
        → Ψ ⊢ Aₘ ⊕ Bₘ
    
    ⊕L : ∀ { m k : Mode } { Ψ : Context } { Aₘ : Prop m } { Bₘ : Prop m } { Cₖ : Prop k }
        → (Ψ , Aₘ) ⊢ Cₖ   →   (Ψ , Bₘ) ⊢ Cₖ
        -----------------------------------------
        → (Ψ , Aₘ ⊕ Bₘ) ⊢ Cₖ 

    -- -- With
    &R : ∀ { m : Mode } { Ψ : Context } { Aₘ Bₘ : Prop m }
        → Ψ ⊢ Aₘ    →   Ψ ⊢ Bₘ
        ------------------------
        → Ψ ⊢ Aₘ & Bₘ

    &L₁ : ∀ { m k : Mode } { Ψ : Context } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → (Ψ , Aₘ) ⊢ Cₖ
        --------------
        → (Ψ , (Aₘ & Bₘ)) ⊢ Cₖ

    &L₂ : ∀ { m k : Mode } { Ψ : Context } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → (Ψ , Bₘ) ⊢ Cₖ
        --------------
        → (Ψ , (Aₘ & Bₘ)) ⊢ Cₖ 
    -- -- Tensor
    ⊗R : ∀ { m : Mode } { Ψ₁ Ψ₂ : Context } { Aₘ Bₘ : Prop m }
        → Ψ₁ ⊢ Aₘ   →   Ψ₂ ⊢ Bₘ
        -------------------------
        → (Ψ₁ ++ Ψ₂) ⊢ Aₘ ⊗ Bₘ

    ⊗L : ∀ { m k : Mode } { Ψ : Context } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → ((Ψ , Aₘ ), Bₘ ) ⊢ Cₖ
        --------------------------
        → (Ψ , (Aₘ ⊗ Bₘ)) ⊢ Cₖ
    -- -- Lolli
    ⊸R : ∀ { m : Mode } { Ψ : Context } { Aₘ Bₘ : Prop m }
        → (Ψ , Aₘ) ⊢ Bₘ
        --------------------
        → Ψ ⊢ Aₘ ⊸ Bₘ

    ⊸L : ∀ { m k : Mode } { Ψ₁ Ψ₂ : Context } { Aₘ Bₘ : Prop m } { Cₖ : Prop k }
        → Ψ₁ ⊢ Aₘ   →   (Ψ₂ , Bₘ) ⊢ Cₖ
        ----------------------------------
        → ((Ψ₁ ++ Ψ₂) , (Aₘ ⊸ Bₘ)) ⊢ Cₖ

    -- Top - no left rule for top
    ⊤R : ∀ { m : Mode } { Ψ : Context }
        ------------------
        → Ψ ⊢ ⊤ { m } 

    -- -- Multiplicative unit
    𝟙R : ∀ { m : Mode } { Ψ : Context }
        → StructRule.W ∈ σ(Ψ)
        -----------------------
        → Ψ ⊢ 𝟙 {m}

    𝟙L : ∀ { m k : Mode } { Ψ : Context } { Cₖ : Prop k }
        → Ψ ⊢ Cₖ
        ----------
        → (Ψ , 𝟙 {m}) ⊢ Cₖ 

    -- -- Down shift
    DownR : ∀ { m k : Mode } { Ψ : Context } { Aₘ : Prop m } { m≥k : m ≥ k }
        → Ψ ≥ˡ m    →   Ψ ⊢ Aₘ
        -----------------------
        → Ψ ⊢ Down[ m≥k ] Aₘ
    
    DownL : ∀ { m l k : Mode } { Ψ : Context } { Aₘ : Prop m } { Cₗ : Prop l } { m≥k : m ≥ k }
        → (Ψ , Aₘ) ⊢ Cₗ 
        ------------------
        → (Ψ , Down[ m≥k ] Aₘ) ⊢ Cₗ
    -- -- Up shift
    UpR : ∀ { m k : Mode } { Ψ : Context } { Aₖ : Prop k } { m≥k : m ≥ k }
        → Ψ ⊢ Aₖ
        -----------
        → Ψ ⊢ Up[ m≥k ] Aₖ

    UpL : ∀ { m k l : Mode } { Ψ : Context } { Aₖ : Prop k } { Cₗ : Prop l } { m≥k : m ≥ k }
        → k ≥ l         →       (Ψ , Aₖ) ⊢ Cₗ
        ----------------------------------------
        → (Ψ , Up[ m≥k ] Aₖ) ⊢ Cₗ  

    -- For all rules taken from Frank Pfenning's notes on sequent calculus: https://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf
    -- Note: Not too sure on allR
    ∀R : ∀ { m : Mode } { Ψ : Context } { Aₘ : Prop m }
        → (substitution : Prop m → Prop m)
        → Ψ ⊢ substitution Aₘ
        -----------------
        → Ψ ⊢ ∀[ Aₘ ]

    -- We encode two versions of for all: one where the proposition being eliminated is weakenable and one where it is not.
    ∀L₁ : ∀ { m k : Mode } { Ψ : Context } { Aₘ : Prop m } { Cₖ : Prop k }
        → (substitution : Terms → Prop m → Prop m)
        → (t : Terms)
        → (Ψ , (substitution t Aₘ)) ⊢ Cₖ
        --------------------------
        → (Ψ , ∀[ Aₘ ]) ⊢ Cₖ

    ∀L₂ : ∀ { m k : Mode } { Ψ : Context } { Aₘ : Prop m } { Cₖ : Prop k }
        → (substitution : Terms → Prop m → Prop m)
        → (t : Terms)
        → StructRule.W ∈ rulesOf (modeOf (∀[ Aₘ ]))
        → ((Ψ , ∀[ Aₘ ]) , (substitution t Aₘ)) ⊢ Cₖ
        ----------------------------------------------
        → (Ψ , (∀[ Aₘ ])) ⊢ Cₖ
        
