open import Data.Vec
open import Data.Nat hiding (_≥_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Logic.Core.Modes

module Logic.Core.Contexts (Atom : Set) (TermAtom : Set) where
  open import Logic.Core.Props Atom
  open import Logic.Core.Terms TermAtom

  Context : ∀ ( m n : ℕ ) → Set
  Context m n = (Vec (Term 0) m) × (Vec (Prop × Mode) n)

  -- Concatenating contexts
  _++ᶜ_ : ∀ { w x y z } → Context w x → Context y z → Context (w + y) (x + z)
  ⟨ terms₁ , props₁ ⟩ ++ᶜ ⟨ terms₂ , props₂ ⟩ = ⟨ terms₁ ++ terms₂ , props₁ ++ props₂ ⟩
  private
    variable
      s n x y z : ℕ
      ts ts₁ ts₂ : Vec (Term s) n
      ps ps₁ ps₂ : Vec (Prop × Mode) x
      t t₁ t₂ : Term s
      Δ Δ' Δ'' Δ₁ Δ₂ Δ₃ Δ₂' Δ₁₂ Δ₂₃ Δ₁₂' Δ₂₃'  : Context x y
      m m₁ m₂ m₃ k l : Mode

  data cWeakenable : Context x y → Set where
    weak/n : cWeakenable ⟨ ts , [] ⟩
    weak/c : cWeakenable Δ → mWeakenable m → cWeakenable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data cContractable : Context x y → Set where
    cont/n : cContractable ⟨ ts , [] ⟩
    cont/c : cContractable Δ → mContractable m → cContractable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data cUnrestricted : Context x y → Set where
    unr/n : cUnrestricted ⟨ ts , [] ⟩
    unr/c : cUnrestricted Δ → cUnrestricted ⟨ proj₁ Δ , ⟨ A , Unrestricted ⟩ ∷ proj₂ Δ ⟩

  data cLinear : Context x y → Set where
    lin/n : cLinear ⟨ ts , [] ⟩
    lin/c : cLinear Δ → cLinear ⟨ proj₁ Δ , ⟨ A , Linear ⟩ ∷ proj₂ Δ ⟩

  data cIrrelevant : Context x y → Set where
    irr/n : cIrrelevant ⟨ ts , [] ⟩
    irr/c : cIrrelevant Δ → cIrrelevant ⟨ proj₁ Δ , (⟨ A , Irrelevant ⟩ ∷ proj₂ Δ) ⟩

  data exh : Context x y → Set where
    exh/n : exh ⟨ ts , [] ⟩
    exh/c : exh Δ → harmless m → exh ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data _≥ᶜ_ : Context x y → Mode → Set where
    N : ⟨ ts , [] ⟩ ≥ᶜ m
    S : Δ ≥ᶜ k → m ≥ k → ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ ≥ᶜ k

  data merge : Context x y → Context x y → Context x y → Set where
    mg/n : merge ⟨ ts , [] ⟩ ⟨ ts , [] ⟩ ⟨ ts , [] ⟩
    mg/c : merge Δ₁ Δ₂ Δ → m₁ ∙ m₂ ⇒ m
      → merge ⟨ proj₁ Δ₁ , (⟨ A , m₁ ⟩ ∷ proj₂ Δ₁) ⟩ ⟨ proj₁ Δ₂ , (⟨ A , m₂ ⟩ ∷ proj₂ Δ₂) ⟩ ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩

  data update : Context x y → Prop × Mode → Prop × Mode → Context x y → Set where
    N : update ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ ⟨ A , m ⟩ ⟨ B , k ⟩ ⟨ proj₁ Δ , (⟨ B , k ⟩ ∷ proj₂ Δ) ⟩

    S : update Δ ⟨ A , m ⟩ ⟨ B , k ⟩ Δ'
      → update ⟨ proj₁ Δ , (⟨ C , l ⟩ ∷ proj₂ Δ) ⟩ ⟨ A , m ⟩ ⟨ B , k ⟩ ⟨ proj₁ Δ' , (⟨ C , l ⟩ ∷ proj₂ Δ') ⟩

  data mayConsume : Context x y → Prop × Mode → Context x y → Set where
    yea : update Δ ⟨ A , m ⟩ ⟨ A , Irrelevant ⟩ Δ'
      → mayConsume Δ ⟨ A , m ⟩ Δ'

    nay : update Δ ⟨ A , m ⟩ ⟨ A , m ⟩ Δ → mContractable m
      → mayConsume Δ ⟨ A , m ⟩ Δ

  data isTerm : Context x y → (Term 0) → Set where
    isTerm/z : isTerm ⟨ t ∷ proj₁ Δ , proj₂ Δ ⟩ t
    isTerm/s : isTerm ⟨ proj₁ Δ , proj₂ Δ ⟩ t₁
      → isTerm ⟨ t₂ ∷ proj₁ Δ , proj₂ Δ ⟩ t₁

  data areTerms : Context x y → Vec (Term 0) n → Set where
    areTerms/z : areTerms Δ []
    areTerms/s : areTerms Δ ts
      → isTerm Δ t
      → areTerms Δ (t ∷ ts)

  data Comparable : Context x y → Context x y → Set where
    comp/z : Comparable ⟨ ts , [] ⟩ ⟨ ts , [] ⟩
    comp/s : Comparable ⟨ ts , ps₁ ⟩ ⟨ ts , ps₂ ⟩
      → Comparable ⟨ ts , ⟨ A , m ⟩ ∷ ps₁ ⟩ ⟨ ts , ⟨ A , k ⟩ ∷ ps₂ ⟩

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

  data mergeGetId : Context x y → Set where
    merge/getid : merge Δ Δ' Δ → exh Δ' → mergeGetId Δ

  merge-getid : ∀ ( Δ : Context x y ) → mergeGetId Δ
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

  cWeaken-to-mWeaken : ∀ { Δ : Context x y } → cWeakenable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ → mWeakenable m
  cWeaken-to-mWeaken (weak/c cW x) = x

  cWeaken-shrink : ∀ { Δ : Context x y } → cWeakenable ⟨ proj₁ Δ , (⟨ A , m ⟩ ∷ proj₂ Δ) ⟩ → cWeakenable ⟨ proj₁ Δ , (proj₂ Δ) ⟩
  cWeaken-shrink (weak/c cW x) = cW 

  ----------------------------------------------------------
  -- Properties of irrelevancy
  ----------------------------------------------------------
  cIrrelevant-to-cWeaken : ∀ { Δ : Context x y } → cIrrelevant Δ → cWeakenable Δ
  cIrrelevant-to-cWeaken irr/n = weak/n
  cIrrelevant-to-cWeaken (irr/c irr) = weak/c (cIrrelevant-to-cWeaken irr) mweak/i

  -- A fully irrelevant context can merge with itself
  cIrrelevant-merge : ∀ { Δ : Context x y } → cIrrelevant Δ → merge Δ Δ Δ
  cIrrelevant-merge irr/n = mg/n
  cIrrelevant-merge (irr/c irr) = mg/c (cIrrelevant-merge irr) i∙i

  ----------------------------------------------------------
  -- Properties of unrestrictedness
  ----------------------------------------------------------
  cUnrestricted-to-cWeaken : ∀ { Δ : Context x y } → cUnrestricted Δ → cWeakenable Δ
  cUnrestricted-to-cWeaken unr/n = weak/n
  cUnrestricted-to-cWeaken (unr/c unr) = weak/c (cUnrestricted-to-cWeaken unr) mweak/u

  cUnrestricted-to-cContract : ∀ { Δ : Context x y } → cUnrestricted Δ → cContractable Δ
  cUnrestricted-to-cContract unr/n = cont/n
  cUnrestricted-to-cContract (unr/c unr) = cont/c (cUnrestricted-to-cContract unr) mcontract/u
  
  -- A fully unrestricted context can merge with itself
  cUnrestricted-merge-id : ∀ { Δ : Context x y }
    → cUnrestricted Δ
    → merge Δ Δ Δ
  cUnrestricted-merge-id unr/n = mg/n
  cUnrestricted-merge-id (unr/c unr) = mg/c (cUnrestricted-merge-id unr) u∙u

  {-
    Properties of the Comparable relation
  -}
  comparable-id : Comparable Δ Δ
  comparable-id {Δ = ⟨ fst , [] ⟩} = comp/z
  comparable-id {Δ = ⟨ fst , ⟨ fst₁ , snd₁ ⟩ ∷ snd ⟩} = comp/s comparable-id

  comparable-trans : Comparable Δ₁ Δ₂ → Comparable Δ₂ Δ₃ → Comparable Δ₁ Δ₃
  comparable-trans comp/z comp/z = comp/z
  comparable-trans (comp/s comp1) (comp/s comp2) = comp/s (comparable-trans comp1 comp2)

  comparable-comm : Comparable Δ₁ Δ₂ → Comparable Δ₂ Δ₁
  comparable-comm comp/z = comp/z
  comparable-comm (comp/s comp) = comp/s (comparable-comm comp)

  ----------------------------------------------------------
  -- Properties of concatenation
  ----------------------------------------------------------
  concat-cWeak : ∀ { Δ } → Δ ≡ Δ₁ ++ᶜ Δ₂ → cWeakenable Δ₁ → cWeakenable Δ₂ → cWeakenable Δ
  concat-cWeak {Δ₁ = ⟨ fst , [] ⟩} {Δ₂ = ⟨ fst₁ , [] ⟩} refl cWeak1 cWeak2 = weak/n
  concat-cWeak {Δ₁ = ⟨ fst , [] ⟩} {Δ₂ = ⟨ fst₁ , .(⟨ _ , _ ⟩) ∷ snd ⟩} refl cWeak1 (weak/c cWeak2 x) = weak/c (concat-cWeak refl weak/n cWeak2) x
  concat-cWeak {Δ₁ = ⟨ fst , .(⟨ _ , _ ⟩) ∷ snd ⟩} {Δ₂ = ⟨ fst₁ , [] ⟩} refl (weak/c cWeak1 x) cWeak2 = weak/c (concat-cWeak refl cWeak1 weak/n) x 
  concat-cWeak {Δ₁ = ⟨ fst , .(⟨ _ , _ ⟩) ∷ snd ⟩} {Δ₂ = ⟨ fst₁ , .(⟨ _ , _ ⟩) ∷ snd₁ ⟩} refl (weak/c cWeak1 x) (weak/c cWeak2 x₁) = weak/c (concat-cWeak refl cWeak1 (weak/c cWeak2 x₁)) x

  concat-cContr : ∀ { Δ } → Δ ≡ Δ₁ ++ᶜ Δ₂ → cContractable Δ₁ → cContractable Δ₂ → cContractable Δ
  concat-cContr {Δ₁ = ⟨ fst , [] ⟩} {Δ₂ = ⟨ fst₁ , [] ⟩} refl cContr1 cContr2 = cont/n
  concat-cContr {Δ₁ = ⟨ fst , [] ⟩} {Δ₂ = ⟨ fst₁ , .(⟨ _ , _ ⟩) ∷ snd₁ ⟩} refl cContr1 (cont/c cContr2 x) = cont/c (concat-cContr refl cont/n cContr2) x 
  concat-cContr {Δ₁ = ⟨ fst , .(⟨ _ , _ ⟩) ∷ snd ⟩} {Δ₂ = ⟨ fst₁ , [] ⟩} refl (cont/c cContr1 x) cContr2 = cont/c (concat-cContr refl cContr1 cont/n) x 
  concat-cContr {Δ₁ = ⟨ fst , .(⟨ _ , _ ⟩) ∷ snd ⟩} {Δ₂ = ⟨ fst₁ , .(⟨ _ , _ ⟩) ∷ snd₁ ⟩} refl (cont/c cContr1 x) (cont/c cContr2 x₁) = cont/c (concat-cContr refl cContr1 (cont/c cContr2 x₁)) x 

  concat-merge : ∀ { w x y z } { Δ₁ Δ₂ Δ₃ : Context w x } { Δ₄ Δ₅ Δ₆ : Context y z } → merge Δ₁ Δ₂ Δ₃ → merge Δ₄ Δ₅ Δ₆ → merge (Δ₁ ++ᶜ Δ₄) (Δ₂ ++ᶜ Δ₅) (Δ₃ ++ᶜ Δ₆)
  concat-merge {x = zero} {z = zero} mg/n mg/n = mg/n
  concat-merge {x = zero} {z = suc z} mg/n (mg/c M2 x) = mg/c (concat-merge mg/n M2) x 
  concat-merge {x = suc x} {z = zero} (mg/c M1 x₁) mg/n = mg/c (concat-merge M1 mg/n) x₁ 
  concat-merge {x = suc x} {z = suc z} (mg/c M1 x₁) (mg/c M2 x₂) = mg/c (concat-merge M1 (mg/c M2 x₂)) x₁

  concat-update-r : ∀ { w x y z A m B k } { Δ₁ Δ₁' : Context w x } { Δ₂ : Context y z } 
    → update Δ₁ ⟨ A , m ⟩ ⟨ B , k ⟩ Δ₁'
    → update (Δ₂ ++ᶜ Δ₁) ⟨ A , m ⟩ ⟨ B , k ⟩ (Δ₂ ++ᶜ Δ₁')
  concat-update-r {z = zero} {Δ₂ = ⟨ fst , [] ⟩} N = N
  concat-update-r {z = zero} {Δ₂ = ⟨ fst , [] ⟩} (S U) = S (concat-update-r U)
  concat-update-r {z = suc z} {Δ₂ = ⟨ fst , x ∷ snd ⟩} U = S (concat-update-r { Δ₂ = ⟨ fst , snd ⟩ } U) 