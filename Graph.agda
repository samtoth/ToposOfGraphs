{-# OPTIONS --cubical --rewriting --with-K #-}

module Graph where

open import Prelude
open import Join
import Open
import Closed

private
  variable
    ℓ : Level

postulate
  𝓋 : ℙ

-- If we are thinking of v as a morphism 1 → Ω
-- then V is the subterminal graph that represents it

-- We will later show how we can fix V to be the graph with a point
-- and no loops
V : Grph
V = wrap (isTrue 𝓋)

open Open 𝓋
open Closed 𝓋



postulate
  ○-dneg : ∀ {A : Set ℓ} → ○ A ≅ ¬ (¬ A)


-- We consider the open modality
-- that is v → P.
-- p^(h(V))(x) ≅ Hom(h(x), p^(h(V))) ≅ Grph(h(x) × h(V), P)
--   vertices of (v → P) := Grph(h(V) × h(V), P) ≅ Grph(h(V), P) ≅ P(V)
--   edges of (v → P) := Grph(h(E) × h(V), P) ≅ Grph(∙ ∙, P)
-- that is ○ P is the complete graph on the nodes of P

-- Then a graph is complete when ○-η is onto
Complete : Grph ℓ → Grph ℓ
Complete G = is-surjective (○-η {_} {G})

-- The closed modality is the pushout 𝓋 ← (𝓋 × G) → G
--    this is called the join 𝓋 * G
--      Span := B ← A → C
--      F : Span → Psh(G)
--      F(B ← A → C) := 𝓋 ← 𝓋 × G → G
--    Hom(h(x), (𝓋 * G))  ≅ Hom(h(x), colim_y(F(y)))
--  ≅ colim_y(Hom(h(x), F(y))) ≅ colim_y(F(y)(x))
-- (𝓋 * G)(V) ≅ colim_y(F(y)(V)) ≅ colim(𝟙 ← G(V) → G(V))

-- A graph is single (has one point) when it is ●-modal
Single : Grph ℓ → Grph ℓ
Single = ●-modal

○●-contr : ∀ {A : Set ℓ} → ○ ● A ≅ Unit {ℓ}
fwd ○●-contr _ = <>
bwd ○●-contr _ = mk-wrap (λ v → *-inl v)
fwd-bwd ○●-contr <> = refl
bwd-fwd ○●-contr (mk-wrap x') = ⊢-ext λ p → inl≡x (x' p) p

-- The product of two presheaves is computed pointwise
-- (f × g)(x) ≅ Hom(h(x), f × g)
--            ≅ Hom(h(x), f) × Hom(h(x), g)
--            ≅ f(x) × g(x)
-- so the vertices of (f × g) = (f × g)(V) ≅ f(V) × g(V)
--   i.e. the product of nodes
-- and the edges are the product of edges.

-- (h(V) × G)(x) ≅ Hom(h(x), h(V) × G) ≅ Hom(x,V) × G(x)
-- (h(V) × G)(V) ≅ Hom(V,V) × G(V) ≅ G(V)
-- (h(V) × G)(E) ≅ Hom(E,V) × G(E) ≅ ∅ × G(E) ≅ ∅

-- You can take a graph and remove
-- all paths to get the discrete graph
-- on the vertex set.
Vertices : Grph ℓ → Grph ℓ
Vertices G = V × G

is-discrete : Grph ℓ → Grph ℓ
is-discrete G = V × G ≅ G


-- The parts of a graph is the pullback
-- of the obvious maps ○ A → ● ○ A ← ● A
Parts : Grph ℓ → Grph ℓ
Parts G = Σ[ O ∈ ○ G ] Σ[ C ∈ ● G ] (●-η O ≡ ●-map ○-η C)
 

Parts-make-whole : ∀ {G : Grph ℓ} → Parts G ≅ G
fwd Parts-make-whole (mk-wrap o , c , p ) = ⌈ *-ind (λ _ → _) o (λ g → {!   !}) c ⌉
bwd Parts-make-whole g = ○-η g , ●-η g , refl
fwd-bwd Parts-make-whole = {!   !}
bwd-fwd Parts-make-whole = {!   !}


postulate
  V-single : Single V
-- fwd V-single = ●-η
-- bwd V-single v = {!   !}
-- fwd-bwd V-single = {!   !}
-- bwd-fwd V-single = {!   !}

is-contr-○V : ○ V ≅ Unit
fwd is-contr-○V p = <>
bwd is-contr-○V p = mk-wrap (λ {p → {!   !}})
fwd-bwd is-contr-○V = {!   !}
bwd-fwd is-contr-○V = {!   !}


-- Bool is the graph: tt  ff
--  with two self loops

data Bool : Grph where
  tt ff : Bool

-- We posulate Arr to be the graph with
-- two points and one Arrow
--  the 'walking arrow graph'
postulate
  Arr : Grph
  Arr-cl : ● Arr ≅ Unit
  Arr-op : ○ Arr ≅ ○ Bool

-- the arrows in G are the global
-- points of Arrs G. 
Arrs : Grph ℓ → Grph ℓ
Arrs G = Arr → G 

-- as a sanity check, the arrows of 
-- V should be V. (the global points of V are empty)
ArrV : Arrs V ≅ V
fwd ArrV arr = V-single .bwd (●-app (●-η arr) (Arr-cl .bwd <>))
bwd ArrV = λ x _ → x
fwd-bwd ArrV (mk-wrap (𝓋 = ⊤)) = refl
bwd-fwd ArrV arrV = funext _ _ (λ x → {!   !})