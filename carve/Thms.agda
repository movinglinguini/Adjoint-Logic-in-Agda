open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Adjoint

module Thms where

  impl_to_expl : Δ ⊢ⁱ ⟨ C , m ⟩ → Δ ⊢ᵉ ⟨ C , m ⟩
  impl_to_expl D1 = {!   !}

  expl_to_impl : Δ ⊢ᵉ ⟨ C , m ⟩ → Δ ⊢ⁱ ⟨ C , m ⟩
  expl_to_impl (id U1 E1) = id U1 (exh_to_cWeakenable E1)
  expl_to_impl (cut M1 G1 G2 D1 D2) with
    merge/getid M2 E1 ← merge-getid _ | merge/getid M3 E2 ← merge-getid _ with
      merge/assoc M4 _ ← merge-assoc M2 M1 | merge/assoc M5 M6 ← merge-assoc M3 (merge-comm M1) with
        refl ← merge-cancl M4 M1 | refl ← merge-cancl M5 (merge-comm M1) with
          refl ← merge-cancl M2 (merge-comm M6) =
            cut M2 (merge-comm M3) M1 G1 {!   !} G2 (exh_to_cContractable E2) (expl_to_impl D1) (expl_to_impl D2) -- TODO
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