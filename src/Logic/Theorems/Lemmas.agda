-- {-# OPTIONS --allow-unsolved-metas #-}

open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality


module Logic.Theorems.Lemmas (Atom : Set) where
  
  open import Logic.Adjoint Atom
  
  {--------------------------------------
  Lemma: Admissibility of exchange
  ----------------------------------------}
  ctxt-exch : ∀ { n } (i : Fin n) → Context (suc n) → Context (suc n)
  ctxt-exch zero (A ∷ B ∷ Δ) = B ∷ A ∷ Δ
  ctxt-exch (suc i) (A ∷ Δ) = A ∷ ctxt-exch i Δ

  exch-weak : ∀ { n } { i : Fin n } { Δ : Context (suc n) } → cWeakenable Δ → cWeakenable (ctxt-exch i Δ)
  exch-weak (weak/c cW x) = {!   !}

  exch-contr : ∀ { n } { i : Fin n } { Δ : Context (suc n) } → cContractable Δ → cContractable (ctxt-exch i Δ)
  exch-contr (cont/c cC x) = {!   !}

  exch-merge : ∀ { n } ( i : Fin n ) { Δ₁ Δ₂ Δ : Context (suc n) }
    → merge Δ₁ Δ₂ Δ 
    → merge (ctxt-exch i Δ₁) (ctxt-exch i Δ₂) (ctxt-exch i Δ)
  exch-merge i (mg/c (mg/c M x₁) x) = {!   !}

  exch-≥ᶜ : ∀ { n } { i : Fin n } { Δ : Context (suc n) }
    → Δ ≥ᶜ m
    → (ctxt-exch i Δ) ≥ᶜ m
  exch-≥ᶜ Δ≥m = {!   !}

  exch-update : ∀ { n } { i : Fin n } { Δ Δ' : Context (suc n) } 
                → update Δ ⟨ A , m ⟩ ⟨ B , l ⟩ Δ' 
                → update (ctxt-exch i Δ) ⟨ A , m ⟩ ⟨ B , l ⟩ (ctxt-exch i Δ')
  exch-update {i = i} {Δ = Δ} U = {!   !}

  exch-consume : ∀ { n } { i : Fin n } { Δ Δ' : Context (suc n) } 
                  → mayConsume Δ ⟨ A , m ⟩ Δ'
                  → mayConsume (ctxt-exch i Δ) ⟨ A , m ⟩ (ctxt-exch i Δ')
  exch-consume (yea U) = yea (exch-update U)
  exch-consume (nay U mC) = nay (exch-update U) mC

  exch-admit : ∀ { q } ( i : Fin q ) { Δ : Context (suc q) } → Δ ⊢ⁱ ⟨ C , k ⟩ → ctxt-exch i Δ ⊢ⁱ ⟨ C , k ⟩
  exch-admit i (id U cW) = id (exch-update U) (exch-weak cW)
  exch-admit i (cut M12 M23 M Δ₁≥m Δ₂≥m m≥k cCΔ₂ D1 D2) 
    = cut (exch-merge i M12) (exch-merge i M23) (exch-merge i M) (exch-≥ᶜ Δ₁≥m) (exch-≥ᶜ Δ₂≥m) m≥k (exch-contr cCΔ₂) (exch-admit i D1) (exch-admit (suc i) D2) 
  exch-admit i (⊕R₁ D) = ⊕R₁ (exch-admit i D) 
  exch-admit i (⊕R₂ D) = ⊕R₂ (exch-admit i D)
  exch-admit i (⊕L MC D1 D2) with MC
  ... | yea U = ⊕L (yea (exch-update U)) (exch-admit (suc i) D1) (exch-admit (suc i) D2)
  ... | nay U mC = ⊕L (nay (exch-update U) mC) (exch-admit (suc i) D1) (exch-admit (suc i) D2)
  exch-admit i (&R D D₁) = &R (exch-admit i D) (exch-admit i D₁)
  exch-admit i (&L₁ MC D) with MC
  ... | yea U = &L₁ (yea (exch-update U)) (exch-admit (suc i) D)
  ... | nay U mC = &L₁ (nay (exch-update U) mC) (exch-admit (suc i) D)
  exch-admit i (&L₂ MC D) with MC
  ... | yea U = &L₂ (yea (exch-update U)) (exch-admit (suc i) D)
  ... | nay U mC = &L₂ (nay (exch-update U) mC) (exch-admit (suc i) D)
  exch-admit i (⊗R M12 M23 M C D1 D2) 
    = ⊗R (exch-merge i M12) (exch-merge i M23) (exch-merge i M) (exch-contr C) (exch-admit i D1) (exch-admit i D2) 
  exch-admit i (⊗L MC D) with MC
  ... | yea U = ⊗L (yea (exch-update U)) (exch-admit (suc (suc i)) D)
  ... | nay U mC = ⊗L (nay (exch-update U) mC) (exch-admit (suc (suc i)) D)
  exch-admit i (⊸R D) = ⊸R (exch-admit (suc i) D)
  exch-admit i (⊸L M12 M23 M mC12 mC23 Δ₁≥m₁ Δ₂≥m₁ cCΔ₂ D1 D2) with mC12 | mC23
  ... | yea U12 | yea U23 = ⊸L {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} (exch-admit i D1) (exch-admit (suc i) D2)
  ... | yea U12 | nay U23 x₂ = {!   !}
  ... | nay U12 x₁ | yea U23 = {!   !}
  ... | nay U12 x₁ | nay U23 x₃ = {!   !}
  exch-admit i (𝟙R cW) = 𝟙R (exch-weak cW)
  exch-admit i (𝟙L MC D) with MC
  ... | yea U = 𝟙L (yea (exch-update U)) (exch-admit i D)
  ... | nay U mC = 𝟙L (nay (exch-update U) mC) (exch-admit i D)
  exch-admit i (↓R M Δ≥k cW D) = ↓R (exch-merge i M) (exch-≥ᶜ Δ≥k) (exch-weak cW) (exch-admit i D) 
  exch-admit i (↓L MC D) with MC
  ... | yea U = ↓L (yea (exch-update U)) (exch-admit (suc i) D)
  ... | nay U mC = ↓L (nay (exch-update U) mC) (exch-admit (suc i) D)
  exch-admit i (↑R D) = ↑R (exch-admit i D)
  exch-admit i (↑L MC k₁≥k D) with MC
  ... | yea U = ↑L (yea (exch-update U)) k₁≥k (exch-admit (suc i) D)
  ... | nay U mC = ↑L (nay (exch-update U) mC) k₁≥k (exch-admit (suc i) D)
  
  exch₀ : (⟨ A , m ⟩ ∷ ⟨ B , l ⟩ ∷ Δ) ⊢ⁱ ⟨ C , k ⟩ → (⟨ B , l ⟩ ∷ ⟨ A , m ⟩ ∷ Δ) ⊢ⁱ ⟨ C , k ⟩
  exch₀ D = exch-admit zero D

  {---------------------------------------
  Lemma: Admissibility of weakening
  ----------------------------------------}
  ctxt-weak : ∀ { m : Mode } 
    → Context n → (Prop × Mode) → mWeakenable m → Context (suc n) 
  ctxt-weak Δ A mW = A ∷ Δ

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
  weak-admit (⊗R M12 M23 M C D1 D2) mWeak with mWeak
  ... | mweak/u = ⊗R (mg/c M12 u∙u) (mg/c M23 u∙u) (mg/c M u∙u) (cont/c C mcontract/u) (weak-admit D1 mweak/u) (weak-admit D2 mweak/u)
  ... | mweak/i = ⊗R (mg/c M12 i∙i) (mg/c M23 i∙i) (mg/c M i∙i) (cont/c C mcontract/i) (weak-admit D1 mweak/i) (weak-admit D2 mweak/i)
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
  weak-admit (↓R M Δ≥k cW D) mWeak with mWeak
  ... | mweak/u = ↓R (mg/c M u∙u) (S Δ≥k u≥m) (weak/c cW mweak/u) (weak-admit D mweak/u)
  ... | mweak/i = ↓R (mg/c M i∙i) (S Δ≥k i≥m) (weak/c cW mweak/i) (weak-admit D mweak/i)
  weak-admit (↓L MC D) mWeak with MC
  ... | yea U = ↓L (yea (S U)) (exch₀ (weak-admit D mWeak)) 
  ... | nay U mC = ↓L (nay (S U) mC) (exch₀ (weak-admit D mWeak))
  weak-admit (↑R D) mWeak = ↑R (weak-admit D mWeak)
  weak-admit (↑L MC x D) mWeak with MC
  ... | yea U = ↑L (yea (S U)) x (exch₀ (weak-admit D mWeak))         
  ... | nay U mC = ↑L (nay (S U) mC) x (exch₀ (weak-admit D mWeak))   