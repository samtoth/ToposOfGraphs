{-# OPTIONS --cubical --rewriting --with-K #-}

module Graph where

open import Prelude
open import Join
import Open
import Closed

private
  variable
    ℓ : Level
    G : Grph ℓ

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
-- data vert : SET where
--   inl : vert
--   inr : G → vert
--   glue : ∀ {g} → inl ≡ inr g

--  we can show that ∀ (x : vert), inl ≡ y,
--      by cases. inl = inl
--         and    inl =⟨sym glue⟩= inr x
--      
--   thus: (𝓋 * G)(V) ≅ 𝟙
--  So there is a single vertex

--  (𝓋 * G)(R) ≅ colim_y(F(y)(E)) ≅  colim(∅ ← ∅ → G(E)) ≅ G(E)
-- with G(E) many loops

-- At first this might seem a strange - or not useful notion
--  but if you consider the global points: that is the set Γ(x) = Hom(𝟙, x)
--    then Γ(● G) ≅ G(E)
--     the edge set

-- A graph is single (has one point) when it is ●-modal
Single : Grph ℓ → Grph ℓ
Single = ●-modal

-- the comple graph on a 1 vertex graph is 𝟙
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



-- V-single : Single V
-- fwd V-single = ●-η
-- bwd V-single v = {!   !}
-- fwd-bwd V-single = {!   !}
-- bwd-fwd V-single = {!   !}

is-contr-○V : ○ V ≅ Unit
fwd is-contr-○V p = <>
bwd is-contr-○V <> = mk-wrap (λ x → {!   !})
fwd-bwd is-contr-○V x = refl
bwd-fwd is-contr-○V (mk-wrap x) = {!   !} -- ⊢-ext (λ p → {!  !})


-- Bool is the graph: tt  ff
--  with two self loops

data Bool : Grph where
  tt ff : Bool

-- We posulate Arr to be the graph with
-- two points and one Arrow
--  the 'walking arrow graph'
postulate
  Arr : Grph
  Arr-op : ○ Arr ≅ ○ Bool


-- we can show that there are two points of Arr, src and tgt
--    these are the representables h(s) and h(t)
src : ○ Arr
src = Arr-op .bwd (○-η tt)

tgt : ○ Arr
tgt = Arr-op .bwd (○-η ff)

-- because it is often the case that what we
-- care about are the global points of a graph,
-- not just the 

-- the arrows in G are the global
-- points of Arrs G. 
Arrs : Grph ℓ → Grph ℓ
Arrs G = Arr → G 

-- We can get the source and target of a particular arrow
Arr-src : {G : Grph ℓ} → (x : Arrs G) → ○ G
Arr-src arr = mk-wrap (λ x → arr ((unwrap src) x))

Arr-tgt : {G : Grph ℓ} → (x : Arrs G) → ○ G
Arr-tgt arr = mk-wrap (λ x → arr ((unwrap tgt) x))

-- and thus carve out the subtype of Arrows in G with a
-- particular src and tgt
Hom : (G : Grph ℓ) → (x y : ○ G) → Grph ℓ
Hom G x y = Σ[ f ∈ Arrs G ] ((Arr-src f ≡ x) × (Arr-tgt f ≡ y))


-- there is an obvious global point of
-- Hom Arr src tgt.
Arr-hom : Hom Arr src tgt
Arr-hom = (λ x → x) , refl , refl


-- The graph of arrows of a graph
-- is complete just when the graph
-- is.
-- Arrs-complete : ∀ {G : Grph ℓ} → Complete G → Complete (Arrs G) 
-- Arrs-complete g = {!   !}

-- as a sanity check, the arrows of 
-- V should be V + V. (the global points of V × Arr are empty) (there are two points)
-- ArrV : Arrs V ≅ (V + V)
-- fwd ArrV arr = {!   !}
-- bwd ArrV = {!   !}
-- fwd-bwd ArrV = {!   !}
-- bwd-fwd ArrV arrV = {!   !} 