{-# OPTIONS --cubical --rewriting --with-K #-}

open import Prelude


-- This is the closed modality with respect to a subingleton φ
module Closed (φ : ℙ) where

  open import Join

  private
    variable
      ℓ : Level

  ●_ : Set ℓ → Set ℓ
  ● A = ⌈ φ * A ⌉

  ●-map : ∀ {A B : Grph ℓ} → (A → B) → ● A → ● B
  ●-map f x = ⌈ *-ind (λ _ → ● _) (λ p → *-inl p) (λ x' → ⌊ *-inr (f x') ⌋) x ⌉

  ●-η : ∀ {A : Set ℓ} → A → ● A
  ●-η = *-inr

  ●-μ : ∀ {A : Set ℓ} → ● ● A → ● A
  ●-μ {A = A} x = ⌈ *-ind (λ _ → ● A) *-inl (λ x' → ⌊ x' ⌋) x ⌉

  ●-idem : ∀ {A : Set ℓ} → ● ● A ≅ ● A
  fwd ●-idem = ●-μ
  bwd ●-idem = *-inr
  fwd-bwd ●-idem x = refl
  bwd-fwd ●-idem x 
    = ⌈ *-ind (λ x' → *-inr (●-μ x') ≡ x') 
          (λ { (φ = ⊤) → refl}) -- inl <> = inr x
          (λ x → ⌊ refl ⌋) x ⌉ 

  
  ●-modal : Set ℓ → Set ℓ
  ●-modal A = A ≅ ● A

  