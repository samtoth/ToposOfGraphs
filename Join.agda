{-# OPTIONS --cubical --rewriting --with-K #-}

module Join where

open import Prelude

private
  variable
    ℓ ℓ' : Level

postulate
  _*_ : (φ : ℙ) → (s : Grph ℓ) → Grph\ φ ℓ

module _ {φ : ℙ} {A : Grph ℓ} where
  *-inl : φ ⊢ ⌈ φ * A  ⌉ 
  *-inl = λ {(φ = ⊤) → <>}

  postulate
    *-inr : A → ⌈ φ * A ⌉

  module _ (B : ⌈ φ * A ⌉ → Grph ℓ') (u : φ ⊩ λ z → B (*-inl z)) (v : (x : A) → B (*-inr x) [ φ ⊢ (λ {(φ = ⊤) → u ⋆}) ]) where
    postulate
      *-ind : (x : ⌈ φ * A ⌉) → B x [ φ ⊢ (λ {(φ = ⊤) → u ⋆}) ]
      *-ind-β : (x : A) → ⌈ *-ind (*-inr x) ⌉ ≡ ⌈ v x ⌉
      {-# REWRITE *-ind-β #-}


  inl≡inr : ∀ {x} → p ∶ φ ⊩ (*-inl p ≡ *-inr x)
  inl≡inr = λ {(φ = ⊤) → refl}
  
  inl≡x : ∀ (x : ⌈ φ * A ⌉) → p ∶ φ ⊩ (*-inl p ≡ x)
  inl≡x x = λ {(φ = ⊤) → ⌈ *-ind (λ t →  *-inl ⋆ ≡ t)
     (λ p → refl) (λ x' → ⌊ inl≡inr {x'} ⋆ ⌋)  x ⌉}

  phi-contr : ∀ {x y : ⌈ φ * A ⌉} → p ∶ φ ⊩ (x ≡ y)
  phi-contr (φ = ⊤) = refl 
    