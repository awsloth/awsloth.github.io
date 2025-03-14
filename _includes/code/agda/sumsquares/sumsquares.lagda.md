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

_$_ : {A B : Type} (f : A → B) (a : A) → B
f $ a = f a

infix 1 _$_

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

_≡⟨_⟩_ : {A : Type} → (p : A) {y z : A} → p ≡ y → y ≡ z → p ≡ z
p ≡⟨ q ⟩ r = trans q r

_∎ : {A : Type} → (a : A) → a ≡ a
a ∎ = refl a

infixr 0 _≡⟨_⟩_
infix 1 _∎

_∘_ : {A B C : Type} → (f : B → C) → (g : A → B) → A → C
_∘_ f g x = f (g x)

_ℕ+_ : ℕ → ℕ → ℕ
zero ℕ+ b = b
suc a ℕ+ b = suc (a ℕ+ b)

_ℕ*_ : ℕ → ℕ → ℕ
zero ℕ* b = zero
suc a ℕ* b = (a ℕ* b) ℕ+ b

ℕ+1-is-suc : (n : ℕ) → n ℕ+ 1 ≡ suc n
ℕ+1-is-suc zero = refl 1
ℕ+1-is-suc (suc n) = ap suc (ℕ+1-is-suc n)

ℕ+-right-cancel : (n : ℕ) → n ℕ+ 0 ≡ n
ℕ+-right-cancel zero = refl _
ℕ+-right-cancel (suc n) = ap suc (ℕ+-right-cancel n)

ℕ+-step : (n m : ℕ) → n ℕ+ suc m ≡ suc (n ℕ+ m)
ℕ+-step zero m = refl (suc m)
ℕ+-step (suc n) m = ap suc (ℕ+-step n m)

ℕ+-comm : (n m : ℕ) → n ℕ+ m ≡ m ℕ+ n
ℕ+-comm zero m = sym $ ℕ+-right-cancel m
ℕ+-comm (suc n) m = (suc n ℕ+ m) ≡⟨ refl _ ⟩
                    suc (n ℕ+ m) ≡⟨ sym $ ℕ+-step n m ⟩
                    (n ℕ+ suc m) ≡⟨ ℕ+-comm n (suc m) ⟩
                    (suc m ℕ+ n) ≡⟨ sym $ ℕ+-step m n  ⟩
                    (m ℕ+ suc n) ∎

data Bool : Type where
  true false : Bool

_≤b_ : ℕ → ℕ → Bool
zero ≤b b = true
suc a ≤b zero = false
suc a ≤b suc b = a ≤b b

if_then_else_ : {A : Type} → Bool → A → A → A
if true then a else _ = a
if false then _ else b = b

regardless : {A : Type} {b : Bool} {a a' p : A}  → (a ≡ p) → (a' ≡ p) → if b then a else a' ≡ p 
regardless {b = true} p q = p
regardless {b = false} p q = q

passforward : {A : Type} → (b : Bool) → (b ≡ true → A) → (b ≡ false → A) → A
passforward true l r = l (refl true)
passforward false l r = r (refl false)

_∸_ : ℕ → ℕ → ℕ
a ∸ zero = a
zero ∸ suc b = zero
suc a ∸ suc b = a ∸ b

-ℕ_ : ℕ → ℤ
-ℕ zero = pos zero
-ℕ suc a = -[ a ]-1

-_ : ℤ → ℤ
- (pos x) = -ℕ x
- -[ x ]-1 = pos (suc x)

double-neg : (x : ℤ) → x ≡ - (- x)
double-neg (pos zero) = refl (pos 0)
double-neg (pos (suc x)) = refl (pos (suc x))
double-neg -[ x ]-1 = refl (-[ x ]-1)

_⊝_ : ℕ → ℕ → ℤ
a ⊝ b = if (a ≤b b) then (-ℕ (b ∸ a)) else pos (a ∸ b) 

ℕ-minus-flips : (a b : ℕ) → - (a ⊝ b) ≡ b ⊝ a
ℕ-minus-flips zero zero = refl (pos 0)
ℕ-minus-flips (suc a) zero = refl (-[ a ]-1)
ℕ-minus-flips zero (suc b) = refl (pos (suc b))
ℕ-minus-flips (suc a) (suc b) = ℕ-minus-flips a b

minus-self-zero : (a : ℕ) → a ⊝ a ≡ pos 0
minus-self-zero zero = refl (pos 0)
minus-self-zero (suc a) = minus-self-zero a

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

+-left-cancel : (z : ℤ) → (pos 0) + z ≡ z
+-left-cancel (pos x) = refl (pos x)
+-left-cancel -[ x ]-1 = refl (-[ x ]-1)

+-right-cancel : (z : ℤ) → z + (pos 0) ≡ z
+-right-cancel (pos x) = ap pos (ℕ+-right-cancel x)
+-right-cancel -[ x ]-1 = refl _

+-comm : (a b : ℤ) → a + b ≡ b + a
+-comm (pos a) (pos b) = ap pos (ℕ+-comm a b)
+-comm (pos a) -[ b ]-1 = refl (pos a + -[ b ]-1)
+-comm -[ a ]-1 (pos b) = refl (-[ a ]-1 + pos b)
+-comm -[ a ]-1 -[ b ]-1 = ap (λ p → -[ suc p ]-1) (ℕ+-comm a b)

neg-right-cancel : (z : ℤ) → z - (pos 0) ≡ z
neg-right-cancel (pos zero) = refl _
neg-right-cancel (pos (suc x)) = refl _
neg-right-cancel -[ x ]-1 = ap -[_]-1 (ℕ+-right-cancel x)

neg-plus-cancel : (z : ℤ) → (- z) + z ≡ pos 0
neg-plus-cancel (pos zero) = refl (pos 0)
neg-plus-cancel (pos (suc x)) = minus-self-zero (suc x)
neg-plus-cancel -[ x ]-1 = minus-self-zero (suc x)

neg-plus-minus-one-neg : (x : ℕ) → (-ℕ x) + -[ 0 ]-1 ≡ -[ x ]-1
neg-plus-minus-one-neg zero = refl -[ 0 ]-1
neg-plus-minus-one-neg (suc x) = ap (-[_]-1 ∘ suc) (ℕ+-right-cancel x) 

*-right-cancel : (z : ℤ) → z * (pos 0) ≡ (pos 0)
*-right-cancel (pos zero) = refl _
*-right-cancel (pos (suc x)) = trans (+-right-cancel (pos x * pos 0)) (*-right-cancel (pos x))
*-right-cancel -[ zero ]-1 = refl _
*-right-cancel -[ suc x ]-1 = trans (neg-right-cancel (-[ x ]-1 * pos 0)) (*-right-cancel -[ x ]-1)

*-left-neg : (z : ℤ) → -[ 0 ]-1 * z ≡ - z
*-left-neg (pos x) = refl (-ℕ x)
*-left-neg -[ x ]-1 = refl (pos (suc x))

*-right-neg : (z : ℤ) → z * -[ 0 ]-1 ≡ - z
*-right-neg (pos zero) = refl (pos zero)
*-right-neg (pos (suc x)) = pos (suc x) * -[ 0 ]-1 ≡⟨ ap (_+ -[ 0 ]-1) (*-right-neg (pos x)) ⟩
                            (- pos x) + -[ 0 ]-1 ≡⟨ neg-plus-minus-one-neg x ⟩
                            (- pos (suc x)) ∎
*-right-neg -[ zero ]-1 = refl (pos 1)
*-right-neg -[ suc x ]-1 = -[ suc x ]-1 * -[ 0 ]-1 ≡⟨ ap (_- -[ 0 ]-1) (*-right-neg -[ x ]-1) ⟩
                           (- -[ x ]-1) - -[ 0 ]-1 ≡⟨ ap (pos ∘ suc) (ℕ+1-is-suc x) ⟩
                           (- -[ suc x ]-1) ∎


neg-is-+-neg : (x y : ℤ) → x - y ≡ x + (- y)
neg-is-+-neg (pos zero) (pos zero) = refl (pos 0)
neg-is-+-neg (pos (suc x)) (pos zero) = sym $ ap (pos ∘ suc) (ℕ+-right-cancel x)
neg-is-+-neg (pos zero) (pos (suc y)) = refl (pos zero - pos (suc y))
neg-is-+-neg (pos (suc x)) (pos (suc y)) = refl (pos (suc x) - pos (suc y))
neg-is-+-neg -[ x ]-1 (pos zero) = ap -[_]-1 (ℕ+-right-cancel x)
neg-is-+-neg -[ x ]-1 (pos (suc y)) = ap -[_]-1 (ℕ+-step x y)
neg-is-+-neg (pos zero) -[ y ]-1 = refl (pos zero - -[ y ]-1)
neg-is-+-neg (pos (suc x)) -[ y ]-1 = refl (pos (suc x) - -[ y ]-1)
neg-is-+-neg -[ x ]-1 -[ y ]-1 = refl (-[ x ]-1 - -[ y ]-1)

neg-distrib : (a b : ℤ) → - (a + b) ≡ (- a) + (- b)
neg-distrib (pos zero) (pos b) = sym $ +-left-cancel (- pos b)
neg-distrib (pos (suc a)) (pos zero) = ap (-[_]-1) (ℕ+-right-cancel a)
neg-distrib (pos (suc a)) (pos (suc b)) = ap (-[_]-1) (ℕ+-step a b)
neg-distrib (pos zero) -[ b ]-1 = refl (pos (suc b))
neg-distrib (pos (suc a)) -[ b ]-1 = ℕ-minus-flips a b
neg-distrib -[ a ]-1 (pos zero) = sym $ ap (pos ∘ suc) (ℕ+-right-cancel a) 
neg-distrib -[ a ]-1 (pos (suc b)) = ℕ-minus-flips b a
neg-distrib -[ a ]-1 -[ b ]-1 = ap (λ y → pos (suc y)) (sym $ ℕ+-step a b)

neg-times-right : (a b : ℤ) → (a * (- b)) ≡ (- (a * b))
neg-times-right (pos zero) b = refl (pos zero)
neg-times-right (pos (suc x)) b = pos (suc x) * (- b)     ≡⟨ refl _ ⟩
                                  pos x * (- b) + (- b)   ≡⟨ ap (_+ (- b)) (neg-times-right (pos x) b)  ⟩
                                  (- (pos x * b)) + (- b) ≡⟨ sym $ neg-distrib (pos x * b) b ⟩
                                  (- (pos x * b + b))     ≡⟨ refl _ ⟩
                                  (- (pos (suc x) * b))   ∎
neg-times-right -[ zero ]-1 b = -[ zero ]-1 * (- b) ≡⟨ *-left-neg (- b) ⟩
                                (- (- b)) ≡⟨ sym $ ap (-_) (*-left-neg b) ⟩
                                (- (-[ zero ]-1 * b)) ∎
neg-times-right -[ suc x ]-1 b = -[ suc x ]-1 * (- b) ≡⟨ refl _ ⟩
                                 -[ x ]-1 * (- b) - (- b) ≡⟨ neg-is-+-neg (-[ x ]-1 * (- b)) (- b) ⟩
                                 -[ x ]-1 * (- b) + (- (- b)) ≡⟨ ap (λ p → p + (- (- b))) (neg-times-right -[ x ]-1 b) ⟩
                                 (- (-[ x ]-1 * b)) + (- (- b)) ≡⟨ sym $ neg-distrib (-[ x ]-1 * b) (- b) ⟩
                                 (- (-[ x ]-1 * b + (- b))) ≡⟨ sym $ ap (-_) (neg-is-+-neg (-[ x ]-1 * b) b) ⟩
                                 (- (-[ x ]-1 * b - b)) ≡⟨ refl _ ⟩
                                 (- (-[ suc x ]-1 * b)) ∎

neg-times-left : (a b : ℤ) → ((- a) * b) ≡ (- (a * b))
neg-times-left (pos zero) b = refl _
neg-times-left (pos (suc a)) b = {!!}
neg-times-left -[ zero ]-1 b = pos 0 + b ≡⟨ +-left-cancel b ⟩
                               b ≡⟨ double-neg b ⟩
                               (- (- b)) ≡⟨ ap -_ (sym $ *-left-neg b) ⟩
                               (- (-[ zero ]-1 * b)) ∎
neg-times-left -[ suc x ]-1 b = {!!}

*-comm : (a b : ℤ) → a * b ≡ b * a
*-comm (pos zero) (pos b) = sym $ *-right-cancel (pos b)
*-comm (pos (suc a)) (pos b) = {!!}
*-comm (pos zero) -[ b ]-1 = sym $ *-right-cancel (-[ b ]-1)
*-comm (pos (suc a)) -[ b ]-1 = {!!}
*-comm -[ zero ]-1 (pos b) = {!*-left-neg!}
*-comm -[ suc a ]-1 (pos b) = {!!}
*-comm -[ zero ]-1 -[ b ]-1 = {!!}
*-comm -[ suc a ]-1 -[ b ]-1 = {!!}

ℕ+-homo : (a b : ℕ) → pos a + pos b ≡ pos (a ℕ+ b)
ℕ+-homo a b = refl _

ℕ*-homo : (a b : ℕ) → pos a * pos b ≡ pos (a ℕ* b)
ℕ*-homo zero b = refl (pos zero)
ℕ*-homo (suc a) b = pos a * pos b + pos b ≡⟨ ap (_+ pos b) (ℕ*-homo a b) ⟩
                    pos (a ℕ* b) + pos b ≡⟨ refl (pos (a ℕ* b) + pos b) ⟩
                    pos ((a ℕ* b) ℕ+ b) ≡⟨ sym (ℕ+-homo (a ℕ* b) b) ⟩
                    pos (a ℕ* b) + pos b ∎

forced-one : (p z : ℤ) → p * z ≡ p → z ≡ pos 1
forced-one p (pos zero) q = {!!}
forced-one p (pos (suc zero)) q = refl (pos 1)
forced-one p (pos (suc (suc z))) q = {!trans (sym q) (*-comm p (pos (suc (suc z))))!}
forced-one p -[ x ]-1 q = {!!}

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

infixr 2 _∔_

data _×_ (A B : Type) : Type where
  _,_ : A → B → A × B

_≡_mod_ : ℤ → ℤ → ℕ → Type
a ≡ b mod p = Σ k ꞉ ℤ , a ≡ b + k * (pos p)

infixr 5 _*_
infixr 4 _+_
infixr 3 _-_

prime : ℤ → Type
prime p = (a : ℤ) → (Σ b ꞉ ℤ , a * b ≡ p) → (a ≡ pos 1) ∔ (a ≡ - (pos 1)) ∔ (a ≡ p) ∔ (a ≡ - p)

_≤_ : ℤ → ℤ → Type
a ≤ b = Σ k ꞉ ℕ , a + (pos k) ≡ b

squares-are-non-negative : (a : ℤ) → (pos 0) ≤ (a * a)
squares-are-non-negative (pos x) = (x ℕ* x) , sym $ ℕ*-homo x x
squares-are-non-negative -[ zero ]-1 = 1 , refl (pos 1)
squares-are-non-negative -[ suc x ]-1 = (((x ℕ* x) ℕ+ (2 ℕ* x)) ℕ+ 1) , {!!}
  where
    IH : pos 0 ≤ (-[ x ]-1 * -[ x ]-1)
    IH = squares-are-non-negative -[ x ]-1

    diff : ℕ
    diff = fst IH

    proof : pos 0 + pos (diff) ≡ -[ x ]-1 * -[ x ]-1
    proof = snd IH

data ℤ[i] : Type where
  _+[_]i : ℤ → ℤ → ℤ[i]

piecewise : {a b c d : ℤ} → a ≡ c → b ≡ d → a +[ b ]i ≡ c +[ d ]i
piecewise (refl _) (refl _) = refl _

-- Need to rename these
_+i_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +[ b ]i) +i (c +[ d ]i) = (a + b) +[ (c + d) ]i

_-i_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +[ b ]i) -i (c +[ d ]i) = (a - b) +[ (c - d) ]i

_*i_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +[ b ]i) *i (c +[ d ]i) = (a * c - b * d) +[ (a * d + b * c) ]i 

_∣_ : ℤ[i] → ℤ[i] → Type
a ∣ b = Σ s ꞉ ℤ[i] , a *i s ≡ b

comp_ : ℤ[i] → ℤ[i]
comp (a +[ b ]i) = (a +[ (- b) ]i)

```

The norm function

```agda
N' : ℤ[i] → ℤ[i]
N' (a +[ b ]i) = (a +[ b ]i) *i (a +[ (- b) ]i)

N : ℤ[i] → ℤ
N (a +[ b ]i) = (a * a + b * b)

norm-is-non-negative : (z : ℤ[i]) → (pos 0) ≤ N z
norm-is-non-negative (pos a +[ pos b ]i) = (a ℕ* a) ℕ+ (b ℕ* b) , pos ((a ℕ* a) ℕ+ (b ℕ* b)) ≡⟨ refl _ ⟩
                                                                  pos (a ℕ* a) + pos (b ℕ* b) ≡⟨ sym $ ap (pos (a ℕ* a) +_) (ℕ*-homo b b) ⟩
                                                                  pos (a ℕ* a) + pos b * pos b  ≡⟨ sym $ ap (_+ pos b * pos b) (ℕ*-homo a a) ⟩
                                                                  pos a * pos a + pos b * pos b ∎
norm-is-non-negative (pos a +[ -[ b ]-1 ]i) = {!!} , {!!}
norm-is-non-negative (-[ a ]-1 +[ pos b ]i) = {!!} , {!!}
norm-is-non-negative (-[ a ]-1 +[ -[ b ]-1 ]i) = {!!} , {!!}

norm-simp-lemma : (z : ℤ[i]) → N' z ≡ ((N z) +[ pos 0 ]i)
norm-simp-lemma (a +[ b ]i) = piecewise real complex
  where
    real : a * a - b * (- b) ≡ a * a + b * b
    real = a * a - b * (- b) ≡⟨ neg-is-+-neg (a * a) (b * (- b)) ⟩
           a * a + (- (b * (- b))) ≡⟨ ap (λ p → a * a + (- p)) (neg-times-right b b)  ⟩
           a * a + (- (- (b * b))) ≡⟨ ap (a * a +_) (sym $ double-neg (b * b)) ⟩
           a * a + b * b ∎

    complex : a * (- b) + b * a ≡ pos 0
    complex = a * (- b) + b * a ≡⟨ ap (_+ b * a) (neg-times-right a b) ⟩
              (- (a * b)) + b * a ≡⟨ ap (- (a * b) +_) (*-comm b a) ⟩
              (- (a * b)) + a * b ≡⟨ neg-plus-cancel (a * b) ⟩
              pos 0 ∎

N-is-homomorphism : (x y : ℤ[i]) → N (x *i y) ≡ (N x) * (N y)
N-is-homomorphism x@(a +[ b ]i) y@(c +[ d ]i) = {!!}
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

norm-1-unit : {u : ℤ[i]} → N u ≡ pos 1 → unit u
norm-1-unit {a +[ b ]i} p = (a +[ - b ]i) , piecewise real complex
  where
    real : a * a - b * (- b) ≡ pos 1
    real = a * a - b * (- b) ≡⟨ neg-is-+-neg (a * a) (b * (- b)) ⟩
           a * a + (- (b * (- b))) ≡⟨ ap (λ y → a * a + - y) (neg-times-right b b) ⟩
           a * a + (- (- (b * b))) ≡⟨ ap (a * a +_) (sym $ double-neg (b * b)) ⟩
           N (a +[ b ]i) ≡⟨ p ⟩
           pos 1 ∎

    complex : a * (- b) + b * a ≡ pos 0
    complex = a * (- b) + b * a ≡⟨ ap (_+ b * a) (neg-times-right a b) ⟩
              - (a * b) + b * a ≡⟨ ap (- (a * b) +_) (*-comm b a) ⟩
              - (a * b) + a * b ≡⟨ neg-plus-cancel (a * b) ⟩
              pos 0 ∎

unit-norm-1 : (u : ℤ[i]) → unit u → N u ≡ pos 1
unit-norm-1 u@(a +[ b ]i) ((c +[ d ]i) , q) = {!!}

all-units : (u : ℤ[i]) → unit u → (u ≡ ((pos 1) +[ (pos 0) ]i))
                                ∔ (u ≡ (-[ 0 ]-1 +[ (pos 0) ]i))
                                ∔ (u ≡ ((pos 0) +[ (pos 1) ]i))
                                ∔ (u ≡ ((pos 0) +[ -[ 0 ]-1 ]i))
all-units u (y , p) = {!!}

associate : ℤ[i] → ℤ[i] → Type
associate a b = Σ u ꞉ ℤ[i] , (unit u) × (b ≡ a *i u)

irreducible : ℤ[i] →  Type
irreducible z = (a : ℤ[i]) → (a ∣ z) → (unit a) ∔ (associate a z)

big-theorem : (z : ℤ[i]) (p : ℤ) → prime p → N z ≡ p → irreducible z
big-theorem z p pr-p n-eq a (b , q) = expand $ pr-p (N a) (N b , equality)
  where
    equality = sym (trans (sym n-eq) (trans (ap N (sym q)) (N-is-homomorphism a b)))

    expand : (N a ≡ pos 1) ∔ (N a ≡ (- pos 1)) ∔ (N a ≡ p) ∔ (N a ≡ (- p)) → unit a ∔ associate a z
    expand (inl x) = inl (norm-1-unit x)
    expand (inr (inl x)) = {!norm-is-non-negative a!}
    expand (inr (inr (inl x))) = inr (b , ({!!} , sym q))
    expand (inr (inr (inr x))) = {!norm-is-non-negative a!}


```
