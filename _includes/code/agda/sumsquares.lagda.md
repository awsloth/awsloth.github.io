# Obtaining the form of sums of squares

In the course I am taking currently on number theory, we looked at numbers which are the sum of two squares, that is

> \\(z \in \mathbb{N}\\) such that \\(a^2 + b^2 = z\\) for \\(a, b \in \mathbb{Z}\\).

Like a lot of questions in number theory, the connection between such numbers feels quite hidden (and to me that's what makes the subject interesting). The key idea here, that makes the connection jump out is instead inspecting the Guassian integers (\\(\mathbb{Z}[i]\\) - numbers of the form \\(a + bi\\) for \\(a, b \in \mathbb{Z}\\)) and the norm function. The norm function over the Guassian integers is defined as follows

> \\(N(a + bi) = (a + bi)(a - bi) = a^2 + b^2\\).

Aha! Therefore the numbers which are sums of two squares are exactly those which are the 'length' of Guassian integers.

## ℤ

```agda
Type = Set

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

data ℤ : Type where
  pos : ℕ → ℤ
  -[_]-1 : ℕ → ℤ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN INTEGER        ℤ    #-}
{-# BUILTIN INTEGERPOS     pos    #-}
{-# BUILTIN INTEGERNEGSUC -[_]-1 #-}

data _≡_ {A : Type} : (x y : A) → Type where
  refl : (x : A) → x ≡ x

infix 0 _≡_

trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl _) q = q

ap : {A B : Type} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
ap f (refl _) = refl _

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym (refl _) = refl _

_ℕ+_ : ℕ → ℕ → ℕ
zero ℕ+ b = b
suc a ℕ+ b = suc (a ℕ+ b)

ℕ+-right-cancel : (n : ℕ) → n ℕ+ 0 ≡ n
ℕ+-right-cancel zero = refl _
ℕ+-right-cancel (suc n) = ap suc (ℕ+-right-cancel n)

data Bool : Type where
  true false : Bool

_≤b_ : ℕ → ℕ → Bool
zero ≤b b = true
suc a ≤b zero = false
suc a ≤b suc b = a ≤b b

if_then_else_ : {A : Type} → Bool → A → A → A
if true then a else _ = a
if false then _ else b = b

_∸_ : ℕ → ℕ → ℕ
a ∸ zero = a
zero ∸ suc b = zero
suc a ∸ suc b = a ∸ b

-ℕ_ : ℕ → ℤ
-ℕ zero = pos zero
-ℕ suc a = -[ a ]-1

-_ : ℤ → ℤ
- pos zero = pos zero
- pos (suc x) = -[ x ]-1
- -[ x ]-1 = pos (suc x)

_⊝_ : ℕ → ℕ → ℤ
a ⊝ b = if (a ≤b b) then (-ℕ (b ∸ a)) else pos (a ∸ b) 

_+_ : ℤ → ℤ → ℤ
pos a + pos b = pos (a ℕ+ b)
pos a + -[ b ]-1 = a ⊝ (suc b)
-[ a ]-1 + pos b = b ⊝ (suc a)
-[ a ]-1 + -[ b ]-1 = -[ suc (a ℕ+ b) ]-1

_-_ : ℤ → ℤ → ℤ
pos a - pos b = a ⊝ b
-[ a ]-1 - pos b = -[ a ℕ+ b ]-1
pos a - -[ b ]-1 = pos a + pos (suc b)
-[ a ]-1 - -[ b ]-1 = b ⊝ a

_*_ : ℤ → ℤ → ℤ
pos zero * b = pos zero
pos (suc x) * b = (pos x) * b + b 
-[ zero ]-1 * pos x = -ℕ x
-[ zero ]-1 * -[ x ]-1 = pos (suc x)
-[ suc x ]-1 * b = -[ x ]-1 * b - b

+-right-cancel : (z : ℤ) → z + (pos 0) ≡ z
+-right-cancel (pos x) = ap pos (ℕ+-right-cancel x)
+-right-cancel -[ x ]-1 = refl _

neg-right-cancel : (z : ℤ) → z - (pos 0) ≡ z
neg-right-cancel (pos zero) = refl _
neg-right-cancel (pos (suc x)) = refl _
neg-right-cancel -[ x ]-1 = ap -[_]-1 (ℕ+-right-cancel x)

*-right-cancel : (z : ℤ) → z * (pos 0) ≡ (pos 0)
*-right-cancel (pos zero) = refl _
*-right-cancel (pos (suc x)) = trans (+-right-cancel (pos x * pos 0)) (*-right-cancel (pos x))
*-right-cancel -[ zero ]-1 = refl _
*-right-cancel -[ suc x ]-1 = trans (neg-right-cancel (-[ x ]-1 * pos 0)) (*-right-cancel -[ x ]-1)

neg-times-right : (a b : ℤ) → (a * (- b)) ≡ (- (a * b))
neg-times-right a (pos zero) = trans (*-right-cancel a) (ap -_ (sym (*-right-cancel a)))
neg-times-right a (pos (suc zero)) = {!!}
neg-times-right a (pos (suc (suc x))) = {!!}
neg-times-right a -[ x ]-1 = {!!}

neg-times-left : (a b : ℤ) → ((- a) * b) ≡ (- (a * b))
neg-times-left (pos zero) b = refl _
neg-times-left (pos (suc zero)) b = {!!}
neg-times-left (pos (suc (suc x))) b = {!!}
neg-times-left -[ x ]-1 b = {!!}

record Σ {A : Type } (B : A → Type) : Type  where
 constructor
  _,_
 field
  fst : A
  snd : B fst
  
open Σ public
infixr 0 _,_

Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

data _∔_ (A B : Type) : Type where
  inl : (a : A) → A ∔ B
  inr : (b : B) → A ∔ B

infixl 2 _∔_

_≡_mod_ : ℤ → ℤ → ℕ → Type
a ≡ b mod p = Σ k ꞉ ℤ , a ≡ b + k * (pos p)

infixr 5 _*_
infixr 4 _+_
infixr 3 _-_

data ℤ[i] : Type where
  _+[_]i : ℤ → ℤ → ℤ[i]

-- Need to rename these
_+i_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +[ b ]i) +i (c +[ d ]i) = (a + b) +[ (c + d) ]i

_-i_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +[ b ]i) -i (c +[ d ]i) = (a - b) +[ (c - d) ]i

_*i_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +[ b ]i) *i (c +[ d ]i) = (a * c - b * d) +[ (a * d + b * c) ]i 

comp_ : ℤ[i] → ℤ[i]
comp (a +[ b ]i) = (a +[ (- b) ]i)

```

The norm function

```agda
N_ : ℤ[i] → ℤ[i]
N (a +[ b ]i) = (a +[ b ]i) *i (a +[ (- b) ]i)

N-simp : ℤ[i] → ℤ[i]
N-simp (a +[ b ]i) = (a * a + b * b) +[ pos 0 ]i

norm-simp-lemma : (z : ℤ[i]) → N z ≡ N-simp z
norm-simp-lemma (a +[ b ]i) = {!!}

N-is-homomorphism : (x y : ℤ[i]) → N (x *i y) ≡ (N x) *i (N y)
N-is-homomorphism (a +[ b ]i) (c +[ d ]i) = {!!}
```

We say a number is a unit if it is a divisor of 1.

```agda
unit : ℤ[i] → Type
unit u = Σ y ꞉ ℤ[i] , u *i y ≡ ((pos 1) +[ (pos 0) ]i)

u-one : unit ((pos 1) +[ (pos 0) ]i)
u-one = (((pos 1) +[ (pos 0) ]i) , refl _)

u-neg-one : unit (-[ 0 ]-1 +[ (pos 0) ]i)
u-neg-one = (-[ 0 ]-1 +[ (pos 0) ]i) , refl _

u-i : unit ((pos 0) +[ (pos 1) ]i)
u-i = (pos 0) +[ -[ 0 ]-1 ]i , refl _

u-neg-i : unit ((pos 0) +[ -[ 0 ]-1 ]i)
u-neg-i = ((pos 0) +[ (pos 1) ]i) , refl _

norm-1-unit : (u : ℤ[i]) → N u ≡ ((pos 1) +[ (pos 0) ]i) → unit u
norm-1-unit (a +[ b ]i) p = (a +[ - b ]i) , p

unit-norm-1 : (u : ℤ[i]) → unit u → N u ≡ ((pos 1) +[ (pos 0) ]i)
unit-norm-1 (a +[ b ]i) ((c +[ d ]i) , q) = {!!}

all-units : (u : ℤ[i]) → unit u → (u ≡ ((pos 1) +[ (pos 0) ]i))
                                ∔ (u ≡ (-[ 0 ]-1 +[ (pos 0) ]i))
                                ∔ (u ≡ ((pos 0) +[ (pos 1) ]i))
                                ∔ (u ≡ ((pos 0) +[ -[ 0 ]-1 ]i))
all-units u (y , p) = {!!}

```
