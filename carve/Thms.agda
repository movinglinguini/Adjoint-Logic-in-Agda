open import Data.Vec
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Adjoint

module Thms where

  impl_to_expl : Δ ⊢ⁱ ⟨ C , m ⟩ → Δ ⊢ᵉ ⟨ C , m ⟩
  impl_to_expl D1 = {!   !}

  {-
    Lemma: Admissibility of weakening
  -}
  weak-admit : Δ ⊢ⁱ ⟨ C , k ⟩ → mWeakenable m → (⟨ A , m ⟩ ∷ Δ) ⊢ⁱ ⟨ C , k ⟩
  weak-admit (id U CW) mWeak = id (S U) (weak/c CW mWeak)
  --- back to this with pen and paper
  weak-admit (cut M1 M2 M3 Δ₁≥m Δ₂≥m m≥k CC D1 D2) mWeak = {!   !}
  weak-admit (⊕R₁ D) mWeak = ⊕R₁ (weak-admit D mWeak)  
  weak-admit (⊕R₂ D) mWeak = ⊕R₂ (weak-admit D mWeak)
  weak-admit (⊕L MC D1 D2) mWeak = {!   !}
  weak-admit (&R D D₁) mWeak = &R (weak-admit D mWeak) (weak-admit D₁ mWeak)
  weak-admit (&L₁ MC D) mWeak with MC
  ... | yea U = &L₁ (yea (S U)) (weak-admit {!   !} {!   !})
  ... | nay U mC = &L₂ (nay (S U) mC) (weak-admit {!   !} {!   !})
  weak-admit (&L₂ MC D) mWeak = {!   !}
  weak-admit (⊗R M12 M23 M C D1 D2) mWeak = {!   !}
  weak-admit (⊗L x D) mWeak = {!   !}
  weak-admit (⊸R D) mWeak = {!   !}
  weak-admit (⊸L x x₁ x₂ x₃ x₄ x₅ x₆ x₇ D D₁) mWeak = {!   !}
  weak-admit (𝟙R x) mWeak = 𝟙R (weak/c x mWeak)
  weak-admit (𝟙L MC D) mWeak with MC
  ... | yea U = 𝟙L (yea (S U)) (weak-admit D mWeak) 
  ... | nay U mC = 𝟙L (nay (S U) mC) (weak-admit D mWeak)
  weak-admit (↓R M Δ≥k cW D) mWeak = {!   !}
  weak-admit (↓L x D) mWeak = {!   !}
  weak-admit (↑R D) mWeak = {!   !}
  weak-admit (↑L x x₁ D) mWeak = {!   !}

  expl_to_impl : Δ ⊢ᵉ ⟨ C , m ⟩ → Δ ⊢ⁱ ⟨ C , m ⟩
  expl_to_impl (id U1 E1) = id U1 (exh_to_cWeakenable E1)
  expl_to_impl (cut M1 G1 G2 D1 D2) with
    merge/getid M2 E1 ← merge-getid _ | merge/getid M3 E2 ← merge-getid _ with
      merge/assoc M4 _ ← merge-assoc M2 M1 | merge/assoc M5 M6 ← merge-assoc M3 (merge-comm M1) with
        refl ← merge-cancl M4 M1 | refl ← merge-cancl M5 (merge-comm M1) with
          refl ← merge-cancl M2 (merge-comm M6) =
            cut M2 (merge-comm M3) M1 G1 {!   !} G2 (exh_to_cContractable E2) (expl_to_impl D1) (expl_to_impl D2)
            -- TODO: for this to work: need to define ≥ only on non-irrelevant modes?
  expl_to_impl (weak U1 W1 D1) = {!   !} -- TODO: prove admissibility of weakening as lemma
  expl_to_impl (contr U1 C1 D1) = {!   !} -- TODO: prove admissibility of contraction as lemma
  expl_to_impl (⊕R₁ D1) = ⊕R₁ (expl_to_impl D1)
  expl_to_impl (⊕R₂ D1) = ⊕R₂ (expl_to_impl D1)
  expl_to_impl (⊕L U1 D1 D2) = ⊕L (yea U1) (expl_to_impl D1) (expl_to_impl D2)
  expl_to_impl (&R D1 D2) = &R (expl_to_impl D1) (expl_to_impl D2)
  expl_to_impl (&L₁ U1 D1) = &L₁ (yea U1) (expl_to_impl D1)
  expl_to_impl (&L₂ U1 D1) = &L₂ (yea U1) (expl_to_impl D1)  
  expl_to_impl (⊗R M1 D1 D2) with
    merge/getid M2 E1 ← merge-getid _ | merge/getid M3 E2 ← merge-getid _ with
      merge/assoc M4 _ ← merge-assoc M2 M1 | merge/assoc M5 M6 ← merge-assoc M3 (merge-comm M1) with
        refl ← merge-cancl M4 M1 | refl ← merge-cancl M5 (merge-comm M1) with
          refl ← merge-cancl M2 (merge-comm M6) =
            ⊗R M2 (merge-comm M3) M1 (exh_to_cContractable E1) (expl_to_impl D1) (expl_to_impl D2)
  expl_to_impl (⊗L U1 D1) = ⊗L (yea U1) (expl_to_impl D1)
  expl_to_impl (⊸R D1) = ⊸R (expl_to_impl D1)
  expl_to_impl (⊸L M1 U1 G1 D1 D2) = {!   !} -- will need associativity of ⋈, dist. of update over ⋈
  expl_to_impl (𝟙R W1) = 𝟙R W1
  expl_to_impl (𝟙L U1 D1) = 𝟙L (yea U1) (expl_to_impl D1)
  expl_to_impl (↓R G1 D1) with
    merge/getid M1 E1 ← merge-getid _ =
      ↓R M1 G1 (exh_to_cWeakenable E1) (expl_to_impl D1)
  expl_to_impl (↓L G1 D1) = ↓L (yea G1) (expl_to_impl D1)
  expl_to_impl (↑R D1) = ↑R (expl_to_impl D1)       
  expl_to_impl (↑L U1 G1 D1) = ↑L (yea U1) G1 (expl_to_impl D1)       