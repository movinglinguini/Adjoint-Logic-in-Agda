open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality

module Logic.Theorems.Thms where

  data Atom : Set where
    unit : Atom

  open import Logic.Adjoint Atom
  --open import Logic.Theorems.Lemmas Atom

  impl_to_expl : Δ ⊢ⁱ ⟨ C , m ⟩ → Δ ⊢ᵉ ⟨ C , m ⟩
  impl_to_expl (id U1 W1) = id U1 {!   !}
  impl_to_expl (cut M1 M2 M3 G1 G2 G3 C1 D1 D2) = {!   !}
  impl_to_expl (⊕R₁ D1) = ⊕R₁ (impl_to_expl D1)
  impl_to_expl (⊕R₂ D1) = ⊕R₂ (impl_to_expl D1)
  impl_to_expl (⊕L (yea U1) D1 D2) = ⊕L U1 (impl_to_expl D1) (impl_to_expl D2)
  impl_to_expl (⊕L (nay U1 C1) D1 D2) = {!   !}
  impl_to_expl (&R D1 D2) = &R (impl_to_expl D1) (impl_to_expl D2)
  impl_to_expl (&L₁ (yea U1) D1) = &L₁ U1 (impl_to_expl D1)
  impl_to_expl (&L₁ (nay U1 C1) D1) = {!   !}
  impl_to_expl (&L₂ (yea U1) D1) = &L₂ U1 (impl_to_expl D1)
  impl_to_expl (&L₂ (nay U1 C1) D1) = {!   !}
  impl_to_expl (⊗R M1 M2 M3 C1 D1 D2) = {!   !}
  impl_to_expl (⊗L (yea U1) D1) = ⊗L U1 (impl_to_expl D1)
  impl_to_expl (⊗L (nay U1 C1) D1) = {!   !}
  impl_to_expl (⊸R D1) = ⊸R (impl_to_expl D1)
  impl_to_expl (⊸L M1 M2 M3 U1 U2 G1 G2 C1 D1 D2) = {!   !}
  impl_to_expl (𝟙R W1) = 𝟙R W1
  impl_to_expl (𝟙L (yea U1) D1) = 𝟙L U1 (impl_to_expl D1)
  impl_to_expl (𝟙L (nay U1 C1) D1) = impl_to_expl D1
  impl_to_expl (↓R M1 G1 W1 D1) = {!   !}
  impl_to_expl (↓L (yea U1) D1) = ↓L U1 (impl_to_expl D1)
  impl_to_expl (↓L (nay U1 C1) D1) = {!   !}
  impl_to_expl (↑R D1) = ↑R (impl_to_expl D1)
  impl_to_expl (↑L (yea U1) G1 D1) = ↑L U1 G1 (impl_to_expl D1)
  impl_to_expl (↑L (nay U1 C1) G1 D1) = {!   !}

  expl_to_impl : Δ ⊢ᵉ ⟨ C , m ⟩ → Δ ⊢ⁱ ⟨ C , m ⟩
  expl_to_impl (id U1 E1) = id U1 (exh_to_cWeakenable E1)
  expl_to_impl (cut M1 G1 G2 D1 D2) with
    merge/getid M2 E1 ← merge-getid _ | merge/getid M3 E2 ← merge-getid _ with
      merge/assoc M4 _ ← merge-assoc M2 M1 | merge/assoc M5 M6 ← merge-assoc M3 (merge-comm M1) with
        refl ← merge-cancl M4 M1 | refl ← merge-cancl M5 (merge-comm M1) with
          refl ← merge-cancl M2 (merge-comm M6) =
            cut M2 (merge-comm M3) M1 G1 {!   !} G2 (exh_to_cContractable E2) (expl_to_impl D1) (expl_to_impl D2)
            -- TODO: for this to work: need to define ≥ only on non-irrelevant modes?
  expl_to_impl (weak U1 W1 D1) = weak-admit2 U1 W1 (expl_to_impl D1)
  expl_to_impl (contr U1 C1 D1) = contr-admit U1 C1 (expl_to_impl D1)
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