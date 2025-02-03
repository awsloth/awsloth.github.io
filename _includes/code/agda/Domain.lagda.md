Being honest I really didn't know what to post first, so I just thought I might as well post something I'm currently trying to learn. After all, isn't one of the best ways you can learn to teach it to others?

In this post I look at formalising some very basic domain theory definitions, namely that of a partially ordered set (or poset for short). I do not claim this to be the best way, but it was the way that made sense to me as I was writing it. I have all the code in the page, but do not explain some of it as it is either self explanatory or can be explored elsewhere for a better explanation than mine. With that said, let's jump in shall we?

## Basic Definitions

> Small note: Although `Set` _is_ a type, as done in the module I take on Type Theory, I prefer to alias it to `Type` for clarity of reading.
```agda
Type = Set
```


Before we jump into any of the mathematics, we first have to define some types to allows us to define and reason about mathematics. We can do this using the standard library but I prefer to start from a clean slate.

We define the natural numbers in the usual way, which serve as a nice example as we go through this post.
```agda
data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ
```

We also define equality in the usual way, along with `ap` as a helper function.
```agda
data _≡_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≡ x

ap : {A B : Type} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
ap f (refl _) = refl (f _)
```

## Relations

We first start by looking at the mathematical definition of a relation.

> A _relation_ on a set \\(X\\) is a subset \\(\sim \\: \subseteq (X \times X)\\). We write \\(x \sim y\\) to mean that \\((x, y) \in \\: \sim\\).

I omit defining this in Agda simply because a subset is a bit subtle to define and involves using the `Fin` type (while this looks to be a simple type, it is one that can be confusing to understand at first and is not the main focus of this post). Instead we define a relation as an inductive type, where we restrict the set to only the relations we want.

To define the relation \\(\leq\\) for the natural numbers, we give two constructors:

- `z≤n` - this is the constructor that says any natural number, \\(n\\), satisfies \\(0 \leq n\\).
- `sn<sm` - this is the constructor that says if we have a pair of natural numbers \\(n, m\\) satisfying \\(n \leq m\\), then we can also say that \\(\text{suc}\\: n ≤ \text{suc}\\: m\\), or equivalently \\(n + 1 \leq m + 1\\).

```agda
data _≤_ : ℕ → ℕ → Type where
  z≤n : (n : ℕ) → zero ≤ n
  sn≤sm : {m n : ℕ} → (n ≤ m) → (suc n) ≤ (suc m)
```

### Properties of Relations

There are some interesting properties of relations that often crop up, the ones we will focus on here are

- reflexivity,
- transitivity, and
- anti-symmetry.

#### Reflexivity

> We call a relation, \\(\sim\\), on a set \\(X\\) _reflexive_, if for all \\(x \in X\\) we have \\(x \sim x\\).

We can define this using a dependent type as follows. Our underlying set is `A` and our relation is `R`. We then use this definition to show that \\(\leq\\) is reflexive.

```agda
reflexive : {A : Set} → (A → A → Type) → Type
reflexive {A} (_R_) = (x : A) → x R x

≤-refl : reflexive (_≤_)
≤-refl zero = z≤n zero
≤-refl (suc n) = sn≤sm (≤-refl n)
```

#### Transitivity

> We call a relation, \\(\sim\\), on a set \\(X\\) _transitive_, for all \\(x, y, z \in X\\) satisfying \(x \sim y\) and \(y \sim z\), we have \\(x \sim z\\).

Similarly to the reflexivity case, we can define transitivity, however we make \\(x, y\\) and \\(z\\) here implicit so that then using this definition is more clear later on. This works in this case because the values can be inferred by the relations `x R y` and `y R z`. 
```agda
transitive : {A : Type} → (A → A → Type) → Type
transitive {A} (_R_) = {x y z : A} → x R y → y R z → x R z

≤-trans : transitive (_≤_)
≤-trans (z≤n _) q = z≤n _
≤-trans (sn≤sm p) (sn≤sm q) = sn≤sm (≤-trans p q)
```

#### Anti-Symmetry

> We call a relation, \\(\sim\\), on a set \\(X\\) _anti-symmetric_, if for all \\(x, y \in X\\), we have that if \\(x \sim y\\) and \\(y \sim x\\), then \\(x = y\\).

As with the other two cases, we define anti-symmetry, also making \\(x\\) and \\(y\\) implicit like in transitivity. We see the first use of `ap` here in the proof that \\(\leq\\) is symmetric, this allows us prove that `x ≡ y` to show that `suc x ≡ suc y`, which we can do using recursion.

```agda
anti-symmetric : {A : Type} → (A → A → Type) → Type
anti-symmetric {A} (_R_) = {x y : A} → x R y → y R x → x ≡ y

≤-anti-sym : anti-symmetric (_≤_)
≤-anti-sym (z≤n _) (z≤n .zero) = refl zero
≤-anti-sym (sn≤sm p) (sn≤sm q) = ap suc (≤-anti-sym p q)
```

### Defining an ordering

Combining these three properties together we form what is a partial order on a set.

> A _partial order_ on a set is a relation that is reflexive, transitive and anti-symmetric. We usually shorten partial order to _poset_.

To combine these conditions into one we require that
```agda
data Poset (A : Type) (_f_ : A → A → Type) : Set₁ where
  poset-axioms : (re : reflexive _f_) → (tr : transitive _f_) → (as : anti-symmetric _f_) → Poset A (_f_)
```

For example, the natural numbers with \\(\leq\\) as we have defined is a poset. We use our earlier proofs to show that \\(\leq\\) satisfies the required properties.

```agda
ℕ-≤-poset : Poset ℕ (_≤_)
ℕ-≤-poset = poset-axioms ≤-refl ≤-trans ≤-anti-sym
```
## End Notes

This has been quite a short post, but hopefully it was a worthwhile read (and hopefully it will spur me on to write some more in depth pieces). Thank you for reading and hopefully see you in another post soon!
