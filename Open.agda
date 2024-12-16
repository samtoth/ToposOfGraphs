{-# OPTIONS --cubical --rewriting --with-K #-}

open import Prelude

-- This is the open modality with respect to a subingleton φ
module Open (φ : ℙ) where

  private
    variable
      ℓ : Level

  ○_ : Set ℓ → Set ℓ
  ○ A = wrap (φ ⊢ A)

  ○-map : ∀ {A B : Grph ℓ} → (A → B) → ○ A → ○ B
  ○-map f (mk-wrap x) = mk-wrap (λ p → f (x p))

  ○-η : ∀ {A : Set ℓ} → A → ○ A
  ○-η a = mk-wrap λ _ → a

  ○-μ : ∀ {A : Set ℓ} → ○ (○ A) → ○ A
  ○-μ a = mk-wrap (λ x → unwrap (unwrap a x) x)

  ○-idem : ∀ {A : Set ℓ} → ○ (○ A) ≅ ○ A
  fwd ○-idem = ○-μ
  bwd ○-idem (mk-wrap a) = mk-wrap (λ x → mk-wrap (λ _ → a x))
  fwd-bwd ○-idem x = refl
  bwd-fwd ○-idem x = refl

  ○-modal : Set ℓ → Set ℓ
  ○-modal A = A ≅ ○ A

  ○-app : ∀ {A B : Grph ℓ} → ○ (A → B) → ○ A → ○ B
  ○-app (mk-wrap f) (mk-wrap x) = mk-wrap λ p → f p (x p)