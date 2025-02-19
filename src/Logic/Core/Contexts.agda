open import Data.Vec
open import Data.Nat hiding (_≥_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Logic.Core.Modes

module Logic.Core.Contexts (Atom : Set) (TermAtom : Set) where
  open import Logic.Core.Props Atom
  open import Logic.Core.Terms TermAtom

  Context : ∀ ( m n : ℕ ) → Set
  Context m n = (Vec Term m) × (Vec (Prop × Mode) n)

  -- Concatenating contexts
  _++ᶜ_ : ∀ { w x y z } → Context w x → Context y z → Context (w + y) (x + z)
  ⟨ terms₁ , props₁ ⟩ ++ᶜ ⟨ terms₂ , props₂ ⟩ = ⟨ terms₁ ++ terms₂ , props₁ ++ props₂ ⟩

  data Concat : ∀ { w x y z } → Context w x → Context y z → Context (w + y) (x + z) → Set where
    concat/ctx : ∀ { w x y z } →  { T₁ : Vec Term w } { T₂ : Vec Term y } { P₁ : Vec (Prop × Mode) x } { P₂ : Vec (Prop × Mode) z } 
      → Concat ⟨ T₁ , P₁ ⟩ ⟨ T₂ , P₂ ⟩ ⟨ T₁ ++ T₂ , P₁ ++ P₂ ⟩   

  variable
    n y z : ℕ
    T : Vec Term y
    Δ Δ' Δ'' Δ₁ Δ₂ Δ₃ Δ₂' Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃'  : Context y n

  data cWeakenable : Context y n → Set where
    weak/n : cWeakenable ⟨ T , [] ⟩
    weak/c : cWeakenable Δ → mWeakenable m → cWeakenable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data cContractable : Context y n → Set where
    cont/n : cContractable ⟨ T , [] ⟩
    cont/c : cContractable Δ → mContractable m → cContractable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data exh : Context y n → Set where
    exh/n : exh ⟨ T , [] ⟩
    exh/c : exh Δ → harmless m → exh ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data _≥ᶜ_ : Context y n → Mode → Set where
    N : ⟨ T , [] ⟩ ≥ᶜ m
    S : Δ ≥ᶜ k → m ≥ k → ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ ≥ᶜ k

  data merge : Context y n → Context y n → Context y n → Set where
    mg/n : merge ⟨ T , [] ⟩ ⟨ T , [] ⟩ ⟨ T , [] ⟩
    mg/c : merge Δ₁ Δ₂ Δ → m₁ ∙ m₂ ⇒ m
      → merge ⟨ proj₁ Δ₁ , (⟨ A , m₁ ⟩ ∷ proj₂ Δ₁) ⟩ ⟨ proj₁ Δ₂ , (⟨ A , m₂ ⟩ ∷ proj₂ Δ₂) ⟩ ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data update : Context y n → Prop × Mode → Prop × Mode → Context y n → Set where
    N : update ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ ⟨ A , m ⟩ ⟨ B , k ⟩ ⟨ proj₁ Δ , (⟨ B , k ⟩ ∷ proj₂ Δ) ⟩

    S : update Δ ⟨ A , m ⟩ ⟨ B , k ⟩ Δ'
      → update ⟨ proj₁ Δ , (⟨ C , l ⟩ ∷ proj₂ Δ) ⟩ ⟨ A , m ⟩ ⟨ B , k ⟩ ⟨ proj₁ Δ' , (⟨ C , l ⟩ ∷ proj₂ Δ') ⟩

  data mayConsume : Context y n → Prop × Mode → Context y n → Set where
    yea : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ'
      → mayConsume Δ ⟨ A , m ⟩ Δ'

    nay : update Δ ⟨ A , m ⟩ ⟨ A , m ⟩ Δ → mContractable m
      → mayConsume Δ ⟨ A , m ⟩ Δ

  data isTerm : Context y n → Term → Set where
    Z : isTerm ⟨ t ∷ proj₁ Δ , proj₂ Δ ⟩ t
    S : isTerm ⟨ proj₁ Δ , proj₂ Δ ⟩ t₁
      → isTerm ⟨ t₂ ∷ proj₁ Δ , proj₂ Δ ⟩ t₁

  ----------------------------------------------------------
  -- Properties of context predicates
  ----------------------------------------------------------

  exh_to_cWeakenable : exh Δ → cWeakenable Δ
  exh_to_cWeakenable exh/n = weak/n 
  exh_to_cWeakenable (exh/c E1 T1) = weak/c (exh_to_cWeakenable E1) (harmless_to_mWeakenable T1)

  exh_to_cContractable : exh Δ → cContractable Δ
  exh_to_cContractable exh/n = cont/n 
  exh_to_cContractable (exh/c E1 T1) = cont/c (exh_to_cContractable E1) (harmless_to_mContractable T1)

  ----------------------------------------------------------
  -- Properties of merge
  ----------------------------------------------------------

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

  merge-cancl : merge Δ₁ Δ₂ Δ → merge Δ₁ Δ₂' Δ → Δ₂ ≡ Δ₂'
  merge-cancl mg/n mg/n = refl
  merge-cancl (mg/c M1 T1) (mg/c M2 T2)
    with refl ← merge-cancl M1 M2 
       | refl ← •-cancl T1 T2 = refl

  data mergeGetId : Context y n → Set where
    merge/getid : merge Δ Δ' Δ → exh Δ' → mergeGetId Δ

  merge-getid : ∀ ( Δ : Context y n ) → mergeGetId Δ
  merge-getid ⟨ fst , [] ⟩ = merge/getid mg/n exh/n
  merge-getid ⟨ fst , ⟨ A , m ⟩ ∷ snd ⟩ with
    merge/getid M1 E1 ← merge-getid ⟨ fst , snd ⟩
      | ∙/getid M2 H1 ← ∙-getid m = merge/getid (mg/c M1 M2) (exh/c E1 H1) 

  ----------------------------------------------------------
  -- Properties of update
  ----------------------------------------------------------

  upd-refl : update Δ ⟨ A , m ⟩ ⟨ B , k ⟩ Δ' → update Δ ⟨ A , m ⟩ ⟨ A , m ⟩ Δ
  upd-refl N = N
  upd-refl (S U1) = S (upd-refl U1)

  upd-symm : update Δ ⟨ A , m ⟩ ⟨ B , k ⟩ Δ' → update Δ' ⟨ B , k ⟩ ⟨ A , m ⟩ Δ
  upd-symm N = N
  upd-symm (S U) = S (upd-symm U)

  -- Note: functionality, transitivity will fail since don't track location; probably want to generalize

  ----------------------------------------------------------
  -- Properties of cWeakenable
  ----------------------------------------------------------

  cWeaken-to-mWeaken : ∀ { Δ : Context y n } → cWeakenable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ → mWeakenable m
  cWeaken-to-mWeaken (weak/c cW x) = x

  cWeaken-shrink : ∀ { Δ : Context y n } → cWeakenable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ → cWeakenable ⟨ proj₁ Δ , (proj₂ Δ) ⟩
  cWeaken-shrink (weak/c cW x) = cW 