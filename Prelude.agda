{-# OPTIONS --cubical --rewriting --confluence-check --with-K #-}

module Prelude where

open import Agda.Primitive public
  renaming (Set to Grph)
open import Agda.Builtin.Sigma public
open import Agda.Primitive.Cubical public
  renaming (I to ℙ; i0 to ⊥; i1 to ⊤; IsOne to isTrue; itIsOne to ⋆) 
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public

coe : {ℓ ℓ′ : _} {A : Grph ℓ} (B : A → Grph ℓ′) {a0 a1 : A} (p : a0 ≡ a1) → B a0 → B a1
coe B refl x = x

trans : {ℓ : _} {A : Grph ℓ} {a0 a1 a2 : A} → a0 ≡ a1 → a1 ≡ a2 → a0 ≡ a2
trans refl q = q

sym :  {ℓ : _} {A : Grph ℓ} {a0 a1 : A}  → a0 ≡ a1 → a1 ≡ a0
sym refl = refl

uip : {ℓ : _} {A : Grph ℓ} {a0 a1 : A} (p q : a0 ≡ a1) → p ≡ q
uip refl refl = refl

ap : {ℓ ℓ′ : _} {A : Grph ℓ} {B : Grph ℓ′} {a0 a1 : A} (f : A → B) → a0 ≡ a1 → f a0 ≡ f a1
ap f refl = refl


record Unit {ℓ} : Grph ℓ where
  constructor <>

data ∅ : Grph where

data _+_ {ℓ ℓ'} (A : Grph ℓ) (B : Grph ℓ') : Grph (ℓ ⊔ ℓ') where
  left : A → A + B
  right : B → A + B

infix 10 _⊢_
infix 10 _⊩_
_⊢_ = Partial
_⊩_ = PartialP

PartialP-syntax = PartialP
syntax PartialP-syntax ϕ (λ z → A) = z ∶ ϕ ⊩ A


open import Agda.Builtin.Cubical.Sub public
  renaming (inc to ⌊_⌋; primSubOut to ⌈_⌉)

infix 4 _[_⊢_]
_[_⊢_] = Sub

Sub-syntax = Sub
syntax Sub-syntax A ϕ (λ z → a) = A [ z ∶ ϕ ⊢ a ]


{-# NO_UNIVERSE_CHECK #-}
record wrap {ℓ} (A : SSet ℓ) : Grph ℓ where
  constructor mk-wrap
  field
    unwrap : A

open wrap public

postulate
  ⊢-ext : ∀ {ℓ} {ϕ} {A : Grph ℓ} {p0 p1 : ϕ ⊢ A} → (z ∶ ϕ ⊩ (p0 z ≡ p1 z)) → mk-wrap p0 ≡ mk-wrap p1
  ⊩-ext : ∀ {ℓ} {ϕ} {A : ϕ ⊢ Grph ℓ} {p0 p1 : ϕ ⊩ A} → (z ∶ ϕ ⊩ _≡_ {A = A z} (p0 z) (p1 z)) → mk-wrap p0 ≡ mk-wrap p1

record iso {ℓ} (A : Grph ℓ) (B : Grph ℓ) : Grph ℓ where
  constructor mk-iso
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → (fwd (bwd x)) ≡ x
    bwd-fwd : ∀ x → (bwd (fwd x)) ≡ x

infix 10 _≅_
_≅_ = iso

open iso public

isom : ∀ {ℓ} (B : Grph ℓ) → Grph (lsuc ℓ)
isom {ℓ} B = Σ (Grph ℓ) λ A → iso A B


postulate
  funext : ∀ {ℓ ℓ'} {A : Grph ℓ} {B : Grph ℓ'} → (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g 

infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Grph ℓ) (B : A → Grph ℓ') → Grph (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

¬ : ∀ {ℓ} → Grph ℓ → Grph ℓ
¬ A = A → wrap (isTrue ⊥)

_×_ : ∀ {ℓ ℓ'} (A : Grph ℓ) (B : Grph ℓ') → Grph (ℓ ⊔ ℓ')
A × B = Σ[ _ ∈ A ] B

×-path : ∀ {ℓ ℓ'} {A : Grph ℓ} {B : Grph ℓ'} {a a' : A} {b b' : B} 
       → a ≡ a' → b ≡ b'
       → (a , b) ≡ (a' , b')
×-path refl refl = refl

is-contr : ∀ {ℓ} → Grph ℓ → Grph ℓ
is-contr A = Σ[ x ∈ A ] (∀ (y : A) → x ≡ y)

is-prop :  ∀ {ℓ} → Grph ℓ → Grph ℓ
is-prop A = ∀ (x y : A) → x ≡ y

postulate
  ∥_∥ : ∀ {ℓ} → Grph ℓ → Grph ℓ
  ∣_∣ : ∀ {ℓ} {A : Grph ℓ} → A → ∥ A ∥
  ∥-∥-ind : ∀ {ℓ ℓ'} {A : Grph ℓ}
             {P : ∥ A ∥ → Grph ℓ'}
         → ((x : _) → is-prop (P x))
         → ((x : A) → P (∣ x ∣))
         → (x : ∥ A ∥) → P x
  ∥-∥-β : ∀ {ℓ ℓ'} {A : Grph ℓ}
             {P : ∥ A ∥ → Grph ℓ'}
         → (P-prop : (x : _) → is-prop (P x))
         → (f : (x : A) → P (∣ x ∣))
         → (a : A)
         → ∥-∥-ind P-prop f ∣ a ∣ ≡ f a
{-# REWRITE ∥-∥-β #-}

fibre : ∀ {ℓ ℓ'} {A : Grph ℓ} {B : Grph ℓ'} → (A → B) → B → Grph _
fibre {A = A} f y = Σ[ x ∈ A ] f x ≡ y

is-equiv :  ∀ {ℓ ℓ'} {A : Grph ℓ} {B : Grph ℓ'} → (A → B) → Grph _
is-equiv f = ∀ y → is-contr (fibre f y)

_≃_ : ∀ {ℓ ℓ'} → Grph ℓ → Grph ℓ' → Grph _
A ≃ B = Σ (A → B) is-equiv 

-- iso-to-equiv : ∀ {ℓ ℓ'} {A : Grph ℓ} {B : Grph ℓ'} 
--              → A ≅ B
--              → A ≃ B
-- iso-to-equiv f 
--   = (f .fwd)
--   , (λ 
--     y → ((f .bwd y) , (f .fwd-bwd y))
--       , (λ where (x , p) → {! ×-path (sym (test p)) (uip _ p) !})) where
--   test : ∀ {x y} → (p : f .fwd x ≡ y) → _
--   test p = trans (sym (f .bwd-fwd _)) (ap (bwd f) p)

is-surjective : ∀ {ℓ ℓ'} {A : Grph ℓ} {B : Grph ℓ'} → (A → B) → Grph _
is-surjective f = ∀ x → ∥ fibre f x ∥

is-embedding : ∀ {ℓ ℓ'} {A : Grph ℓ} {B : Grph ℓ'} → (A → B) → Grph _
is-embedding f = ∀ x → is-prop (fibre f x)

Grph\ : (ϕ : ℙ) (ℓ : Level) → _
Grph\ ϕ ℓ = Grph ℓ [ _ ∶ ϕ ⊢ Unit ]