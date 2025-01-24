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

  data _≥_ : Mode → Mode → Set where
    u≥α : ∀ { α : Mode } → Unrestricted ≥ α
    α≥i : ∀ { α : Mode } → α ≥ Irrelevant
    l≥l : Linear ≥ Linear

  -- TODO: PROVE IT IS A PREORDER

  data _∙_⇒_ : Mode → Mode → Mode → Set where
    u∙u : Unrestricted ∙ Unrestricted ⇒ Unrestricted
    i∙α : ∀ { α : Mode } → Irrelevant ∙ α ⇒ α
    α∙i : ∀ { α : Mode } → α ∙ Irrelevant ⇒ α


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

  PropM = Prop × Mode
  Context : ∀ ( n : ℕ )→ Set
  Context n = Vec (Prop × Mode) n
 
  data merge : ∀ { n } → Context n → Context n → Context n → Set where
    mg/n : merge [] [] []
    mg/c : ∀ { n } { α₁ α₂ α A } → { Δ₁ Δ₂ Δ : Context n }
          → merge Δ₁ Δ₂ Δ → α₁ ∙ α₂ ⇒ α
          → merge (⟨ A , α₁ ⟩ ∷ Δ₁) (⟨ A , α₂ ⟩ ∷ Δ₂) (⟨ A , α ⟩ ∷ Δ)

  data cWeakenable : ∀ { n } → Context n → Set where
    weak/n : cWeakenable []
    weak/c : ∀ { n m A } → { Δ : Context n } 
      → mWeakenable m
      → cWeakenable (⟨ A , m ⟩ ∷ Δ)

  data cContractable : ∀ { n } → Context n → Set where
    cont/n : cContractable []
    cont/c : ∀ { n m A } → { Δ : Context n } 
      → mContractable m
      → cContractable (⟨ A , m ⟩ ∷ Δ)
    
  data update : ∀ { n } → Context n → Prop × Mode → Prop × Mode → Context n → Set where
    N : ∀ { n } → { Δ : Context n } { A B : Prop } { m k : Mode }
      ------------------
      → update (⟨ A , m ⟩ ∷ Δ) (⟨ A , m ⟩) (⟨ B , k ⟩) (⟨ B , k ⟩ ∷ Δ)

    S : ∀ { n } → { Δ Δ' : Context n } { A B C : Prop } { m k l : Mode }
      →  update (Δ) (⟨ A , m ⟩) (⟨ B , k ⟩) (Δ')
      ---------- 
      →  update (⟨ C , l ⟩ ∷ Δ) (⟨ A , m ⟩) (⟨ B , k ⟩) (⟨ C , l ⟩ ∷ Δ')

  data mayConsume : ∀ { n } → Context n → Prop × Mode → Context n → Set where
    yea : ∀ { n } → { Δ Δ' : Context n } { A : Prop } { m : Mode }
      → update (Δ) (⟨ A , m ⟩) (⟨ A , Irrelevant ⟩) (Δ')
      ---------
      → mayConsume Δ ⟨ A , m ⟩ Δ'
      
    nay : ∀ { n } → { Δ : Context n } { A : Prop } { m : Mode }
      → update (Δ) (⟨ A , m ⟩) (⟨ A , m ⟩) (Δ)
      → mContractable m
      -----
      → mayConsume Δ ⟨ A , m ⟩ Δ


  data _≥ᶜ_ : ∀ { n } → Context n → Mode → Set where
    N : ∀ { m } → [] ≥ᶜ m
    S : ∀ { n } { m k A } → { Δ : Context n }
      → Δ ≥ᶜ k → m ≥ k
      → (⟨ A , m ⟩ ∷ Δ) ≥ᶜ k


  data _⊢_ : ∀ { n } → Context n → (Prop × Mode) → Set where
    id : ∀ { n } { m } { Δ Δ' : Context n } { A : Prop }
      → update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ'  → cWeakenable Δ'
      ------------------------------ 
      → Δ ⊢ ⟨ A , m ⟩

    cut : ∀ { n } → { m k : Mode } → { Δ Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ : Context n } → { A C : Prop }
      → merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → m ≥ k
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m
      → cContractable Δ₂
      → Δ₁₂ ⊢ ⟨ A , m ⟩
      → (⟨ A , m ⟩ ∷ Δ₂₃) ⊢ ⟨ C , k ⟩
      -----------
      → Δ ⊢ ⟨ C , k ⟩

    ⊕R₁ : ∀ { n } → { Δ : Context n } { A B : Prop } { m : Mode }
      → Δ ⊢ ⟨ A , m ⟩
      ------------------- 
      → Δ ⊢ ⟨ A ⊕ B , m ⟩ 
    
    ⊕R₂ : ∀ { n } → { Δ : Context n } { A B : Prop } { m : Mode }
      → Δ ⊢ ⟨ B , m ⟩
      ------------------- 
      → Δ ⊢ ⟨ A ⊕ B , m ⟩ 

    ⊕L : ∀ { n } { Δ Δ' : Context n } { A B C : Prop } { m k : Mode }
      → mayConsume Δ ⟨ A ⊕ B , m ⟩ Δ' 
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩ → (⟨ B , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ---------------------- 
      → Δ ⊢ ⟨ C , k ⟩ 

    &R : ∀ { n } { Δ : Context n } { A B : Prop } { m : Mode }
      → Δ ⊢ ⟨ A , m ⟩ → Δ ⊢ ⟨ B , m ⟩
      --------------------- 
      → Δ ⊢ ⟨ A & B , m ⟩

    &L₁ : ∀ { n } { Δ Δ' : Context n } { A B C : Prop } { m k : Mode }
      → mayConsume Δ ⟨ A & B , m ⟩ Δ' 
      →  (⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ---------------------- 
      → Δ ⊢ ⟨ C , k ⟩

    &L₂ : ∀ { n } { Δ Δ' : Context n } { A B C : Prop } { m k : Mode }
      → mayConsume Δ ⟨ A & B , m ⟩ Δ' 
      →  (⟨ B , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ---------------------- 
      → Δ ⊢ ⟨ C , k ⟩

    ⊗R : ∀ { n } → { m : Mode } → { Δ Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ : Context n } → { A B : Prop }
      → merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → cContractable Δ₂
      → Δ₁₂ ⊢ ⟨ A , m ⟩ → Δ₂₃ ⊢ ⟨ B , m ⟩
      -----------------
      → Δ ⊢ ⟨ A ⊗ B , m ⟩

    ⊗L : ∀ { n } { Δ Δ' : Context n } { A B C : Prop } { m k : Mode }
      → mayConsume Δ ⟨ A ⊗ B , m ⟩ Δ'
      → (⟨ B , m ⟩ ∷ ⟨ A , m ⟩ ∷ Δ') ⊢ ⟨ C , k ⟩
      ------------
      → Δ ⊢ ⟨ C , k ⟩

    ⊸R : ∀ { n } { Δ : Context n } { A B : Prop } { m : Mode }
      → (⟨ A , m ⟩ ∷ Δ) ⊢ ⟨ B , m ⟩ 
      --------
      → Δ ⊢ ⟨ A ⊸ B , m ⟩ 

    ⊸L : ∀ { n } → { m k : Mode } → { Δ Δ₁ Δ₂ Δ₃ Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃' : Context n } → { A B C : Prop }
      → merge Δ₁ Δ₂ Δ₁₂ → merge Δ₂ Δ₃ Δ₂₃ → merge Δ₁₂ Δ₃ Δ
      → mayConsume Δ₁₂ ⟨ A ⊸ B , m ⟩ Δ₁₂'
      → mayConsume Δ₂₃ ⟨ A ⊸ B , m ⟩ Δ₂₃'
      → Δ₁ ≥ᶜ m → Δ₂ ≥ᶜ m
      → cContractable Δ₂
      → Δ₁₂ ⊢ ⟨ A , m ⟩
      → (⟨ B , m ⟩ ∷ Δ₂₃) ⊢ ⟨ C , k ⟩
      -----------
      → Δ ⊢ ⟨ C , k ⟩

    𝟙R : ∀ { n } { Δ : Context n } { m }
      → cWeakenable Δ
      --------
      → Δ ⊢ ⟨ 𝟙 , m ⟩

    𝟙L : ∀ { n } { Δ Δ' : Context n } { m k } { C }
      → mayConsume Δ ⟨ 𝟙 , m ⟩ Δ'
      → Δ' ⊢ ⟨ C , k ⟩
      → Δ ⊢ ⟨ C , k ⟩

  ∙-comm : ∀ { M1 M2 M } → M1 ∙ M2 ⇒ M → M2 ∙ M1 ⇒ M
  ∙-comm u∙u = u∙u 
  ∙-comm i∙α = α∙i
  ∙-comm α∙i = i∙α

  ∙-func : ∀ { M1 M2 M M' } → M1 ∙ M2 ⇒ M → M1 ∙ M2 ⇒ M' → M ≡ M'
  ∙-func u∙u u∙u = refl
  ∙-func i∙α i∙α = refl
  ∙-func i∙α α∙i = refl
  ∙-func α∙i i∙α = refl 
  ∙-func α∙i α∙i = refl

  ∙-irrel-is-id : ∀ { M1 M2 } → M1 ∙ Irrelevant ⇒ M2 → M1 ≡ M2
  ∙-irrel-is-id i∙α = refl
  ∙-irrel-is-id α∙i = refl

  data ∙assoc : ∀ { M1 M2 M12 M3 M : Mode } →  M1 ∙ M2 ⇒ M12 → M12 ∙ M3 ⇒ M → Set where
    ∙/assoc : ∀ { M1 M2 M12 M3 M M23 } { D1 : M1 ∙ M2 ⇒ M12 } { D2 : M12 ∙ M3 ⇒ M } 
      → M1 ∙ M23 ⇒ M → M2 ∙ M3 ⇒ M23
      ----------
      → ∙assoc D1 D2

  ∙-assoc : ∀ { M1 M2 M12 M3 M } ( D1 : M1 ∙ M2 ⇒ M12 ) ( D2 : M12 ∙ M3 ⇒ M ) → ∙assoc D1 D2
  ∙-assoc u∙u u∙u = ∙/assoc u∙u u∙u
  ∙-assoc i∙α u∙u = ∙/assoc i∙α u∙u
  ∙-assoc α∙i u∙u = ∙/assoc u∙u i∙α
  ∙-assoc i∙α i∙α = ∙/assoc i∙α i∙α
  ∙-assoc α∙i i∙α = ∙/assoc i∙α i∙α
  ∙-assoc u∙u α∙i = ∙/assoc u∙u α∙i
  ∙-assoc i∙α α∙i = ∙/assoc i∙α α∙i
  ∙-assoc α∙i α∙i = ∙/assoc α∙i i∙α

  merge-comm : ∀ { n } { Δ₁ Δ₂ Δ : Context n } → merge Δ₁ Δ₂ Δ → merge Δ₂ Δ₁ Δ
  merge-comm mg/n = mg/n
  merge-comm (mg/c D x) = mg/c (merge-comm D) (∙-comm x)

  merge-func : ∀ { n } { Δ₁ Δ₂ Δ Δ' : Context n } → merge Δ₁ Δ₂ Δ → merge Δ₁ Δ₂ Δ' → Δ ≡ Δ'
  merge-func mg/n mg/n = refl
  merge-func (mg/c m1 x) (mg/c m2 x₁) with merge-func m1 m2 | ∙-func x x₁
  ... | refl | refl = refl

  data mergeAssoc : ∀ { n } { Δ₁ Δ₂ Δ₁₂ Δ₃ Δ : Context n } →  merge Δ₁ Δ₂ Δ₁₂ → merge Δ₁₂ Δ₃ Δ → Set where
    merge/assoc : ∀ { n } { Δ₁ Δ₂ Δ₁₂ Δ₃ Δ Δ₂₃ : Context n } { D1 : merge Δ₁ Δ₂ Δ₁₂ } { D2 : merge Δ₁₂ Δ₃ Δ } 
      → merge Δ₁ Δ₂₃ Δ → merge Δ₂ Δ₃ Δ₂₃
      ----------
      → mergeAssoc D1 D2

  merge-assoc : ∀ { n }{ Δ₁ Δ₂ Δ₁₂ Δ₃ Δ : Context n }( D1 : merge Δ₁ Δ₂ Δ₁₂ ) ( D2 : merge Δ₁₂ Δ₃ Δ ) → mergeAssoc D1 D2
  merge-assoc mg/n mg/n = merge/assoc mg/n mg/n
  merge-assoc (mg/c D1 x) (mg/c D2 x₁) with merge-assoc D1 D2 | ∙-assoc x x₁
  ... | merge/assoc x₂ x₃ | ∙/assoc x₄ x₅ = merge/assoc (mg/c x₂ x₄) (mg/c x₃ x₅)


      
      
