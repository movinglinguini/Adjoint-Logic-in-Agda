open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import Adjoint

module Thms where

  impl_to_expl : Δ ⊢ⁱ ⟨ C , m ⟩ → Δ ⊢ᵉ ⟨ C , m ⟩
  impl_to_expl D1 = {!   !}

  {-
    Lemma: Admissibility of exchange
  -}
  ctxt-exch : ∀ { n } (i : Fin n) → Context (suc n) → Context (suc n)
  ctxt-exch zero (A ∷ B ∷ Δ) = B ∷ A ∷ Δ
  ctxt-exch (suc i) (A ∷ Δ) = A ∷ ctxt-exch i Δ

  exch-weak : ∀ { n } { i : Fin n } { Δ : Context (suc n) } → cWeakenable Δ → cWeakenable (ctxt-exch i Δ)
  exch-weak {_} { i } { Δ = Δ } (weak/c cW mWeak) with ctxt-exch i Δ
  ... | ⟨ A , m ⟩ ∷ Δ' = {!   !} 

  exch-update : ∀ { n } { i : Fin n } { Δ Δ' : Context (suc n) } 
                → update Δ ⟨ A , m ⟩ ⟨ B , l ⟩ Δ' 
                → update (ctxt-exch i Δ) ⟨ A , m ⟩ ⟨ B , l ⟩ (ctxt-exch i Δ')
  exch-update N = {!   !}
  exch-update (S U) = {!   !}
  
  exch-admit : ∀ { q } ( i : Fin q ) { Δ : Context (suc q) } → Δ ⊢ⁱ ⟨ C , l ⟩ → ctxt-exch i Δ ⊢ⁱ ⟨ C , l ⟩
  exch-admit i D = {!   !}

  exch₀ : (⟨ A , m ⟩ ∷ ⟨ B , l ⟩ ∷ Δ) ⊢ⁱ ⟨ C , k ⟩ → (⟨ B , l ⟩ ∷ ⟨ A , m ⟩ ∷ Δ) ⊢ⁱ ⟨ C , k ⟩
  exch₀ D = {!   !}


  {---------------------------------------
    Lemma: Admissibility of weakening
  ----------------------------------------}
  weak-admit : Δ ⊢ⁱ ⟨ C , k ⟩ → mWeakenable m → (⟨ A , m ⟩ ∷ Δ) ⊢ⁱ ⟨ C , k ⟩
  weak-admit (id U CW) mWeak = id (S U) (weak/c CW mWeak)
  --- back to this with pen and paper
  weak-admit (cut M1 M2 M3 Δ₁≥m Δ₂≥m m≥k CC D1 D2) mWeak = {!   !}
  weak-admit (⊕R₁ D) mWeak = ⊕R₁ (weak-admit D mWeak)  
  weak-admit (⊕R₂ D) mWeak = ⊕R₂ (weak-admit D mWeak)
  weak-admit (⊕L MC D1 D2) mWeak with MC
  ... | yea U = ⊕L (yea (S U)) (exch₀ (weak-admit D1 mWeak)) (exch₀ (weak-admit D2 mWeak))
  ... | nay U mC = ⊕L (nay (S U) mC) (exch₀ (weak-admit D1 mWeak)) (exch₀ (weak-admit D2 mWeak))
  weak-admit (&R D D₁) mWeak = &R (weak-admit D mWeak) (weak-admit D₁ mWeak)
  weak-admit (&L₁ MC D) mWeak with MC
  ... | yea U = &L₁ (yea (S U)) (exch₀ (weak-admit D mWeak))
  ... | nay U mC = &L₁ (nay (S U) mC) (exch₀ (weak-admit D mWeak))
  weak-admit (&L₂ MC D) mWeak with MC
  ... | yea U = &L₂ (yea (S U)) (exch₀ (weak-admit D mWeak))
  ... | nay U mC = &L₂ (nay (S U) mC) (exch₀ (weak-admit D mWeak))
  weak-admit (⊗R M12 M23 M C D1 D2) mWeak = {!   !}
  weak-admit (⊗L MC D) mWeak with MC
  ... | yea U = ⊗L (yea (S U)) (exch-admit (Fin.suc zero) (exch₀ (weak-admit D mWeak)))
  ... | nay U mC = ⊗L (nay (S U) mC) (exch-admit (Fin.suc zero) (exch₀ (weak-admit D mWeak)))
  weak-admit (⊸R D) mWeak = ⊸R (exch₀ (weak-admit D mWeak))
  weak-admit (⊸L M12 M23 M mC12 mC23 Δ₁≥m₁ Δ₂≥m₁ cCΔ₂ D1 D2) mWeak with mC12 | mC23
  ... | yea U12 | yea U23 = {!   !}
  ... | yea U12 | nay U23 x₂ = {!   !}
  ... | nay U12 x₁ | yea U23 = {!   !}
  ... | nay U12 x₁ | nay U23 x₃ = {!   !}
  weak-admit (𝟙R x) mWeak = 𝟙R (weak/c x mWeak)
  weak-admit (𝟙L MC D) mWeak with MC
  ... | yea U = 𝟙L (yea (S U)) (weak-admit D mWeak) 
  ... | nay U mC = 𝟙L (nay (S U) mC) (weak-admit D mWeak)
  weak-admit (↓R M Δ≥k cW D) mWeak = {!   !}
  weak-admit (↓L MC D) mWeak with MC
  ... | yea U = ↓L (yea (S U)) (exch₀ (weak-admit D mWeak)) 
  ... | nay U mC = ↓L (nay (S U) mC) (exch₀ (weak-admit D mWeak))
  weak-admit (↑R D) mWeak = ↑R (weak-admit D mWeak)
  weak-admit (↑L MC x D) mWeak with MC
  ... | yea U = ↑L (yea (S U)) x (exch₀ (weak-admit D mWeak))
  ... | nay U mC = ↑L (nay (S U) mC) x (exch₀ (weak-admit D mWeak))
    
  expl_to_impl : Δ ⊢ᵉ ⟨ C , m ⟩ → Δ ⊢ⁱ ⟨ C , m ⟩
  expl_to_impl (id U1 E1) = id U1 (exh_to_cWeakenable E1)
  expl_to_impl (cut M1 G1 G2 D1 D2) with
    merge/getid M2 E1 ← merge-getid _ | merge/getid M3 E2 ← merge-getid _ with
      merge/assoc M4 _ ← merge-assoc M2 M1 | merge/assoc M5 M6 ← merge-assoc M3 (merge-comm M1) with
        refl ← merge-cancl M4 M1 | refl ← merge-cancl M5 (merge-comm M1) with
          refl ← merge-cancl M2 (merge-comm M6) =
            cut M2 (merge-comm M3) M1 G1 {!   !} G2 (exh_to_cContractable E2) (expl_to_impl D1) (expl_to_impl D2)
            -- TODO: for this to work: need to define ≥ only on non-irrelevant modes?
  expl_to_impl (weak U1 W1 D1) = {!   !} --TODO: prove admissibility of weakening as lemma
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
  expl_to_impl (↓R G1 D1) = {!   !}
  -- with
  --   merge/getid M1 E1 ← merge-getid _ =
  --     ↓R M1 G1 (exh_to_cWeakenable E1) (expl_to_impl D1) 
  expl_to_impl (↓L G1 D1) = ↓L (yea G1) (expl_to_impl D1)
  expl_to_impl (↑R D1) = ↑R (expl_to_impl D1)                     
  expl_to_impl (↑L U1 G1 D1) = ↑L (yea U1) G1 (expl_to_impl D1)           