# Formalising my Mathematics research paper using Agda

In this post I will step through formalising the paper I wrote for my research module. I will cover, category theory in the first section and the simply typed lambda calculus in the second.

## Category Theory

Before we define anything we have to think about universes. A pretty existential comment I know, but really not something as complicated as it sounds, we aren't getting into multiverse theory don't worry! A universe is just a set which contains all the elements we talk about, for example considering the set of all sets is much larger than any conceivable set, so we have to define a bigger universe (this is not strictly what I want to say, but hey ho). Agda lets us set the 'level' of the universe we want to work with, typically this is just `Set`, but when things become more complex, for example, when defining a function from `Set → Set → Set`, we cannot 'contain' this in that universe, so we have to move up a level and use `Set₁`. Agda gives us a way of dealing with this automatically using the `Level` type. Though normally I would like to define this from scratch there is not much point, so I will import this from `Agda.Primitive`. 

```agda
open import Agda.Primitive
```

We first start by defining the notion of a Category.

A category consists of the following

- A collection of objects
- A collection of morphisms between objects
- A composition operation, \(\circ\), for morphisms
- An identity morphism for every object, denoted \(1_A\) for object \(A\)

All satisfying

- Associativity: \(f \circ (g \circ h) = (f \circ g) \circ h\)
- Identity: \(f \circ 1_A = f = 1_B \circ f\)

A lot of this (all of it) is stolen from agda-categories library
```agda
record Category (p u l : Level) : Set (lsuc (p ⊔ u ⊔ l)) where
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set p
    _⇒_ : Obj → Obj → Set u
    _≈_ : ∀ {A B} → (A ⇒ B) → (A ⇒ B) → Set l

    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    id  : ∀ {A} → (A ⇒ A)

  field
    assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ (g ∘ f)) ≈ ((h ∘ g) ∘ f)
    identᵣ : ∀ {A B} {f : A ⇒ B} → (f ∘ id) ≈ f
    identₗ : ∀ {A B} {f : A ⇒ B} → (id ∘ f) ≈ f
    ident² : ∀ {A} → (id ∘ id{A}) ≈ id {A}
```

Examples:

- Set
- Vec
- Category with a single element

```agda
data 𝟙 : Set where
  ⋆ : 𝟙

data morphs : 𝟙 → 𝟙 → Set where
  same : (a : 𝟙) → morphs a a
  
𝟙-cat : Category lzero lzero lzero
𝟙-cat = record
         { Obj = 𝟙
         ; _⇒_ = morphs
         ; _≈_ = λ x y → 𝟙
         ; _∘_ = comp
         ; id = ident
         ; assoc = ⋆
         ; identᵣ = ⋆
         ; identₗ = ⋆
         ; ident² = ⋆
         }
  where
    comp : {A B C : 𝟙} → morphs B C → morphs A B → morphs A C
    comp (same _) f = f

    ident : {A : 𝟙} → morphs A A
    ident {A} = same A
```

### Functor

This is kinda confusing


### Op

## Morphisms

We discuss functions and injective and sujectiveness.

```agda
data _≡_ {u} {A : Set u} : A → A → Set u where
  refl : (x : A) → x ≡ x

ap : ∀ {u} {A B : Set u} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
ap f (refl _) = refl (f _)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

record Σ {A : Set} (B : A → Set) : Set where
  constructor
    _,_
  field
    fst : A
    snd : B fst

open Σ

data surjective {A B : Set} : Set where
  axiom : (f : A → B) → ((b : B) → Σ {A} (λ a → f a ≡ b)) → surjective 

data injective {A B : Set} : Set where
  axiom : (f : A → B) → ((a b : A) → f a ≡ f b → a ≡ b) → injective

data monoₛ {A B C : Set} : Set₁ where
  axiom : (f : A → B) → ((g h : C → A) → ((c : C) → f (g c) ≡ f (h c)) → ((c : C) → g c ≡ h c)) → monoₛ

inj→mono : {A B C : Set} → injective{A}{B} → monoₛ{A}{B}{C}
inj→mono (axiom f p) = axiom f (λ g h q c' → p (g c') (h c') (q c'))

mono→inj : {A B C : Set} → monoₛ{A}{B}{C} → injective{A}{B}
mono→inj {A} {B} {C} (axiom f p) = axiom f (λ a b q → p {!!} {!!} {!!} {!!})

data epiₛ {A B C : Set} : Set₁ where
  axiom : (f : A → B) → ((i j : B → C) → ((a : A) → i (f a) ≡ j (f a)) → ((b : B) → i b ≡ j b)) → epiₛ

sur→epi : {A B C : Set} → surjective{A}{B} → epiₛ{A}{B}{C}
sur→epi {A} {B} {C} (axiom f p) = axiom f λ i j q b → {!p b!}

epi→sur : {A B C : Set} → epiₛ{A}{B}{C} → surjective{A}{B}
epi→sur (axiom f p) = axiom f {!!}
```

### Epi and Mono morphisms

A monophism \(f\) is called a _monomorphism_ if for every \(g, h\) we have that \(f \circ g = f \circ h \implies g = h\).

```agda
-- data mono (c : Category {!!} {!!} {!!}) : Set where
-- p : ∀ {A B C : Obj c} {f : B ⇒ C} {g h : A ⇒ B} → (f ∘ g ≃ f ∘ h) → g ≃ h
```
