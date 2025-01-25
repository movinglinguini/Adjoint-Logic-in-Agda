open import Data.Bool
open import Data.Vec
open import Data.Nat hiding (_≥_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module CarveADJ where
  data Mode : Set where
    Linear : Mode
    Unrestricted : Mode
    Irrelevant : Mode
    -- ⊥ : Mode

  data mWeakenable : Mode → Set where
    mweak/u : mWeakenable Unrestricted
    mweak/i : mWeakenable Irrelevant

  data mContractable : Mode → Set where
    mcontract/u : mContractable Unrestricted
    mcontract/i : mContractable Irrelevant

  data _∙_⇒_ : Mode → Mode → Mode → Set where
    u∙u : Unrestricted ∙ Unrestricted ⇒ Unrestricted
    i∙i : Irrelevant ∙ Irrelevant ⇒ Irrelevant
    i∙l : Irrelevant ∙ Linear ⇒ Linear
    l∙i : Linear ∙ Irrelevant ⇒ Linear

  data Atom : Set where
    unit : Atom

  data Prop : Set where
    -- An arbitrary proposition
    `_  : (A : Atom) → Prop
    -- Implication
    _⊸_ : Prop → Prop → Prop
    -- Tensor
    _⊗_ : Prop → Prop → Prop
    -- Unit
    𝟙 : Prop
    -- Top
    ⊤ : Prop
    -- Plus - Using the binary relation rather than the n-ary version for simplicity
    _⊕_ : Prop → Prop → Prop
    -- With - Using the binary version rather than the n-ary version for simplicity
    _&_ : Prop → Prop → Prop
    ↑[_][_]_ : Mode → Mode → Prop → Prop
    ↓[_][_]_ : Mode → Mode → Prop → Prop

  PropM = Prop × Mode
  Context : ∀ ( n : ℕ ) → Set
  Context n = Vec (Prop × Mode) n

  variable
    n : ℕ
    A B C : Prop
    Δ Δ' Δ₁ Δ₂ Δ₃ Δ₂' Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃'  : Context n
    m k l m' m₁ m₂ m₃ m₂' m₁₂ m₂₃ : Mode

  data _≥_ : Mode → Mode → Set where
    u≥m : Unrestricted ≥ m
    m≥i : m ≥ Irrelevant
    l≥l : Linear ≥ Linear

  -- ≥ is a preorder

  ≥-refl : m ≥ m
  ≥-refl {Linear} = l≥l
  ≥-refl {Unrestricted} = u≥m
  ≥-refl {Irrelevant} = m≥i

  ≥-trans : m₁ ≥ m₂ → m₂ ≥ m₃ → m₁ ≥ m₃
  ≥-trans u≥m u≥m = u≥m
  ≥-trans u≥m m≥i = u≥m
  ≥-trans u≥m l≥l = u≥m
  ≥-trans m≥i m≥i = m≥i
  ≥-trans l≥l m≥i = m≥i
  ≥-trans l≥l l≥l = l≥l

  data merge : Context n → Context n → Context n → Set where
    mg/n : merge [] [] []
    mg/c : merge Δ₁ Δ₂ Δ → m₁ ∙ m₂ ⇒ m
      → merge (⟨ A , m₁ ⟩ ∷ Δ₁) (⟨ A , m₂ ⟩ ∷ Δ₂) (⟨ A , m ⟩ ∷ Δ)

  data cWeakenable : Context n → Set where
    weak/n : cWeakenable []
    weak/c : cWeakenable Δ → mWeakenable m → cWeakenable (⟨ A , m ⟩ ∷ Δ)

  data cContractable : Context n → Set where
    cont/n : cContractable []
    cont/c : cContractable Δ → mContractable m → cContractable (⟨ A , m ⟩ ∷ Δ)

  data exh : Context n → Set where
    cont/n : exh []
    cont/c : exh Δ → exh (⟨ A , Irrelevant ⟩ ∷ Δ)

  data update : Context n → Prop × Mode → Prop × Mode → Context n → Set where
    N : update (⟨ A , m ⟩ ∷ Δ) (⟨ A , m ⟩) (⟨ B , k ⟩) (⟨ B , k ⟩ ∷ Δ)

    S : update Δ (⟨ A , m ⟩) (⟨ B , k ⟩) Δ'
      ----------------------------------------------------------
      →  update (⟨ C , l ⟩ ∷ Δ) (⟨ A , m ⟩) (⟨ B , k ⟩) (⟨ C , l ⟩ ∷ Δ')

  data mayConsume : Context n → Prop × Mode → Context n → Set where
    yea : update Δ (⟨ A , m ⟩) (⟨ A , Irrelevant ⟩) Δ'
      ----------------------------------------------------------
      → mayConsume Δ ⟨ A , m ⟩ Δ'

    nay : update Δ (⟨ A , m ⟩) (⟨ A , m ⟩) Δ → mContractable m
      ----------------------------------------------------------
      → mayConsume Δ ⟨ A , m ⟩ Δ

  data _≥ᶜ_ : Context n → Mode → Set where
    N : [] ≥ᶜ m
    S : Δ ≥ᶜ k → m ≥ k → (⟨ A , m ⟩ ∷ Δ) ≥ᶜ k

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

  data ∙assoc : m₁ ∙ m₂ ⇒ m₁₂ → m₁₂ ∙ m₃ ⇒ m → Set where
    ∙/assoc : {D1 : m₁ ∙ m₂ ⇒ m₁₂} {D2 : m₁₂ ∙ m₃ ⇒ m}
      → m₁ ∙ m₂₃ ⇒ m → m₂ ∙ m₃ ⇒ m₂₃ → ∙assoc D1 D2

  ∙-assoc : (D1 : m₁ ∙ m₂ ⇒ m₁₂) (D2 : m₁₂ ∙ m₃ ⇒ m) → ∙assoc D1 D2
  ∙-assoc u∙u u∙u = ∙/assoc u∙u u∙u
  ∙-assoc i∙i i∙i = ∙/assoc i∙i i∙i
  ∙-assoc i∙i i∙l = ∙/assoc i∙l i∙l
  ∙-assoc i∙l l∙i = ∙/assoc i∙l l∙i
  ∙-assoc l∙i l∙i = ∙/assoc l∙i i∙i

  merge-comm : merge Δ₁ Δ₂ Δ → merge Δ₂ Δ₁ Δ
  merge-comm mg/n = mg/n
  merge-comm (mg/c D T) = mg/c (merge-comm D) (∙-comm T)

  merge-func : merge Δ₁ Δ₂ Δ → merge Δ₁ Δ₂ Δ' → Δ ≡ Δ'
  merge-func mg/n mg/n = refl
  merge-func (mg/c M1 T1) (mg/c M2 T2)
    with refl ← merge-func M1 M2
       | refl ← ∙-func T1 T2 = refl

  data mergeAssoc : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₁₂ Δ₃ Δ → Set where
    merge/assoc : {D1 : merge Δ₁ Δ₂ Δ₁₂} {D2 : merge Δ₁₂ Δ₃ Δ} → merge Δ₁ Δ₂₃ Δ → merge Δ₂ Δ₃ Δ₂₃
      → mergeAssoc D1 D2

  merge-assoc : ∀ (D1 : merge Δ₁ Δ₂ Δ₁₂) (D2 : merge Δ₁₂ Δ₃ Δ) → mergeAssoc D1 D2
  merge-assoc mg/n mg/n = merge/assoc mg/n mg/n
  merge-assoc (mg/c D1 T1) (mg/c D2 T2)
    with merge/assoc M3 M4 ← merge-assoc D1 D2
       | ∙/assoc T3 T4 ← ∙-assoc T1 T2 = merge/assoc (mg/c M3 T3) (mg/c M4 T4)

  •-cancl : m₁ ∙ m₂ ⇒ m → m₁ ∙ m₂' ⇒ m → m₂ ≡ m₂'
  •-cancl u∙u u∙u = refl
  •-cancl i∙i i∙i = refl
  •-cancl i∙l i∙l = refl
  •-cancl l∙i l∙i = refl

  merge-cancl : merge Δ₁ Δ₂ Δ → merge Δ₁ Δ₂' Δ → Δ₂ ≡ Δ₂'
  merge-cancl mg/n mg/n = refl
  merge-cancl (mg/c M1 T1) (mg/c M2 T2)
    with refl ← merge-cancl M1 M2 
       | refl ← •-cancl T1 T2 = refl

  data _⊢ⁱ_ : Context n → (Prop × Mode) → Set where

    id : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ' → cWeakenable Δ'
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A , m ⟩

    cut : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → m ≥ k
      → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩
      → (⟨ A , m ⟩ ∷ Δ₂₃) ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊕R₁ : Δ ⊢ⁱ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊕ B , m ⟩

    ⊕R₂ : Δ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊕ B , m ⟩

    ⊕L : mayConsume Δ ⟨ A ⊕ B , m ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩ → (⟨ B , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    &R : Δ ⊢ⁱ ⟨ A , m ⟩ → Δ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A & B , m ⟩

    &L₁ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    &L₂ : mayConsume Δ ⟨ A & B , m ⟩ Δ'
      →  (⟨ B , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊗R : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩ → Δ₂₃ ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊗ B , m ⟩

    ⊗L : mayConsume Δ ⟨ A ⊗ B , m ⟩ Δ'
      → (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ⊸R : (⟨ A , m ⟩ ∷ Δ) ⊢ⁱ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ A ⊸ B , m ⟩

    ⊸L : merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → mayConsume Δ₁₂ ⟨ A ⊸ B , m ⟩ Δ₁₂'
      → mayConsume Δ₂₃ ⟨ A ⊸ B , m ⟩ Δ₂₃'
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m → cContractable Δ₂
      → Δ₁₂ ⊢ⁱ ⟨ A , m ⟩
      → (⟨ B , m ⟩ ∷ Δ₂₃) ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    𝟙R : cWeakenable Δ
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ 𝟙 , m ⟩

    𝟙L : mayConsume Δ ⟨ 𝟙 , m ⟩ Δ' → Δ' ⊢ⁱ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , k ⟩

    ↓R : merge Δ₁ Δ₂ Δ
      → Δ₁ ≥ᶜ m → cWeakenable Δ₂
      → Δ₁ ⊢ⁱ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ ↓[ m ][ k ] A , m ⟩

    ↓L : mayConsume Δ ⟨ ↓[ m ][ k ] A , m ⟩ Δ'
      → (⟨ A , m ⟩ ∷ Δ') ⊢ⁱ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , l ⟩

    ↑R : Δ ⊢ⁱ ⟨ A , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ ↑[ m ][ k ] A , k ⟩

    ↑L : mayConsume Δ ⟨ ↑[ k ][ m ] A , k ⟩ Δ' → k ≥ l
      → (⟨ A , k ⟩ ∷ Δ') ⊢ⁱ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ⁱ ⟨ C , l ⟩

  data _⊢ᵉ_ : Context n → (Prop × Mode) → Set where

    id : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ' → exh Δ'
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A , m ⟩

    cut : merge Δ₁ Δ₂ Δ
      → Δ₁ ≥ᶜ m → m ≥ k
      → cContractable Δ₂
      → Δ ⊢ᵉ ⟨ A , m ⟩
      → (⟨ A , m ⟩ ∷ Δ₂) ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    weak : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ'
      → mWeakenable m → Δ' ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    contr : update Δ ⟨ A , m ⟩ ⟨ A , m ⟩ Δ
      → mContractable m → (⟨ A , m ⟩ ∷ Δ) ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ⊕R₁ᵉ : Δ ⊢ᵉ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊕ B , m ⟩

    ⊕R₂ᵉ : Δ ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊕ B , m ⟩

    ⊕Lᵉ : update Δ (⟨ A ⊕ B , m ⟩) (⟨ A ⊕ B , Irrelevant ⟩) Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩ → (⟨ B , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    &Rᵉ : Δ ⊢ᵉ ⟨ A , m ⟩ → Δ ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A & B , m ⟩

    &L₁ᵉ : update Δ ⟨ A & B , m ⟩ ⟨ A & B , Irrelevant ⟩ Δ'
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    &L₂ᵉ : update Δ ⟨ A & B , m ⟩ ⟨ A & B , Irrelevant ⟩ Δ'
      →  (⟨ B , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ⊗Rᵉ : merge Δ₁ Δ₂ Δ
      → Δ₁ ⊢ᵉ ⟨ A , m ⟩ → Δ₂ ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊗ B , m ⟩

    ⊗Lᵉ : update Δ ⟨ A ⊗ B , m ⟩ ⟨ A ⊗ B , Irrelevant ⟩ Δ'
      → (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ⊸Rᵉ : (⟨ A , m ⟩ ∷ Δ) ⊢ᵉ ⟨ B , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ A ⊸ B , m ⟩

    ⊸Lᵉ : merge Δ₁ Δ₂ Δ'
      → update Δ ⟨ A ⊸ B , m ⟩ ⟨ A ⊸ B , Irrelevant ⟩ Δ'
      → Δ₁ ≥ᶜ m → Δ₁ ⊢ᵉ ⟨ A , m ⟩
      → (⟨ B , m ⟩ ∷ Δ₂) ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    𝟙Rᵉ : cWeakenable Δ
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ 𝟙 , m ⟩

    𝟙Lᵉ : update Δ ⟨ 𝟙 , m ⟩ ⟨ 𝟙 , Irrelevant ⟩ Δ' → Δ' ⊢ᵉ ⟨ C , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , k ⟩

    ↓Rᵉ : Δ ≥ᶜ m → Δ ⊢ᵉ ⟨ A , m ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ ↓[ m ][ k ] A , m ⟩

    ↓Lᵉ : update Δ ⟨ ↓[ m ][ k ] A , m ⟩ ⟨ ↓[ m ][ k ] A , Irrelevant ⟩ Δ'
      → (⟨ A , m ⟩ ∷ Δ') ⊢ᵉ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , l ⟩

    ↑Rᵉ : Δ ⊢ᵉ ⟨ A , k ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ ↑[ m ][ k ] A , k ⟩

    ↑Lᵉ : update Δ ⟨ ↑[ k ][ m ] A , k ⟩ ⟨ ↑[ k ][ m ] A , Irrelevant ⟩ Δ'
      → k ≥ l → (⟨ A , k ⟩ ∷ Δ') ⊢ᵉ ⟨ C , l ⟩
      ----------------------------------------------------------
      → Δ ⊢ᵉ ⟨ C , l ⟩