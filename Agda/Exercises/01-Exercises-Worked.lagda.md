# Week 01 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 01-Exercises-Worked where

open import prelude hiding (not-is-involution)
```

## Part I: Writing functions on Booleans, natural numbers and lists (★/★★)

### Exercise 1 (★)

In the lectures we defined `&&` (logical and) on `Bool` by pattern matching on
the leftmost argument only.

*NB*: We didn't get round to doing this in the lecture, but see `_&&_` in
      [introduction.lagda.md](../Lecture-Notes/introduction.lagda.md).

**Define** the same operation but this time by pattern matching (case splitting)
  on both arguments.

```agda
_&&'_ : Bool → Bool → Bool
false &&' false = false
true  &&' false = false
false &&' true  = false
true  &&' true  = true
```

One advantage of this definition is that it reads just like a Boolean truth
table. Later on in this exercise sheet, we will see a disadvantange of this more
verbose definition.

### Exercise 2 (★)

**Define** `xor` (excluse or) on `Bool`. Exclusive or is true if and only if
*exactly one* of its arguments is true.

```agda
_xor_ : Bool → Bool → Bool
true xor true = false
true xor false = true
false xor true = true
false xor false = false
```

### Exercise 3 (★)

**Define** the exponential and factorial functions on natural numbers.

If you do things correctly, then the examples should compute correctly, i.e. the
proof that 3 ^ 4 ≡ 81 should simply be given by `refl _` which says that the
left hand side and the right hand side compute to the same value.

```agda
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example = refl 81 -- refl 81 should fill the hole here

_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) * (n !)

!-example : 4 ! ≡ 24
!-example = refl 24 -- refl 24 should fill the hole here
```

### Exercise 4 (★)

We can recursively compute the maximum of two natural numbers as follows.
```agda
max : ℕ → ℕ → ℕ
max zero    m       = m
max (suc n) zero    = suc n
max (suc n) (suc m) = suc (max n m)
```

**Define** the minimum of two natural numbers analogously.

```agda
min : ℕ → ℕ → ℕ
min 0       n       = 0
min (suc m) 0       = 0
min (suc m) (suc n) = suc (min m n)

min-example : min 5 3 ≡ 3
min-example = refl 3 -- refl 3 should fill the hole here
```

### Exercise 5 (★)

Use pattern matching on lists to **define** `map`.

This function should behave as follows:
`map f [x₁ , x₂ , ... , xₙ] = [f x₁ , f x₂ , ... , f xₙ]`.
That is, `map f xs` applies the given function `f` to every
element of the list `xs` and returns the resulting list.

```agda
map : {X Y : Type} → (X → Y) → List X → List Y
map f [] = []
map f (x :: xs) = (f x) :: (map f xs)

map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl _ -- refl _ should fill the hole here

                   -- We write the underscore, because we don't wish to repeat
                   -- the relatively long "4 :: 5 :: 6 :: []" and Agda can
                   -- figure out what is supposed to go there.
```

### Exercise 6 (★★)

**Define** a function `filter` that takes predicate `p : X → Bool` and a list
  `xs` that returns the list of elements of `xs` for which `p` is true.

For example, filtering the non-zero elements of the list [4 , 3 , 0 , 1 , 0]
should return [4 , 3 , 1], see the code below.

```agda
filter : {X : Type} (p : X → Bool) → List X → List X
filter p [] = []
filter p (x :: xs) = if (p x) then (x :: fxs) else fxs where fxs = filter p xs

is-non-zero : ℕ → Bool
is-non-zero zero    = false
is-non-zero (suc _) = true

filter-example : filter is-non-zero (4 :: 3 :: 0 :: 1 :: 0 :: []) ≡ 4 :: 3 :: 1 :: []
filter-example = refl _ -- refl _ should fill the hole here
```

## Part II: The identity type of the Booleans (★/★★)

In the lectures we saw a definition of `≣` on natural numbers where the idea was
that `x ≣ y` is a type which either has precisely one element, if `x` and `y`
are the same natural number, or else is empty, if `x` and `y` are different.

### Exercise 1 (★)

**Define** `≣` for Booleans this time.

```agda
_≣_ : Bool → Bool → Type
{-- if if_then_else_ were universe polymorphic: a ≣ b = if (a xor b) then 𝟘 else 𝟙 --}
true  ≣ true  = 𝟙
false ≣ true  = 𝟘
true  ≣ false = 𝟘
false ≣ false = 𝟙
```

### Exercise 2 (★)

**Show** that for every Boolean `b` we can find an element of the type `b ≣ b`.

```agda
Bool-refl : (b : Bool) → b ≣ b
Bool-refl true = ⋆
Bool-refl false = ⋆

```

### Exercise 3 (★★)

Just like we did in the lectures for natural numbers, **show** that we can go
back and forth between `a ≣ b` and `a ≡ b`.

*NB*: Again, we didn't have time to do this in the lectures, but see
      [introduction.lagda.md](../Lecture-Notes/introduction.lagda.md),
      specifically the functions `back` and `forth` there.

```agda
≡-to-≣ : (a b : Bool) → a ≡ b → a ≣ b
≡-to-≣ true true (refl true) = ⋆
≡-to-≣ true false ()
≡-to-≣ false true ()
≡-to-≣ false false (refl false)= ⋆

≣-to-≡ : (a b : Bool) → a ≣ b → a ≡ b
≣-to-≡ true true ⋆ = refl true
≣-to-≡ true false ()
≣-to-≡ false true ()
≣-to-≡ false false ⋆ = refl false
```

## Part III: Proving in Agda (★★/★★★)

We now turn to *proving* things in Agda: one of its key features.

For example, here is a proof that `not (not b) ≡ b` for every Boolean `b`.

```agda
not-is-involution : (b : Bool) → not (not b) ≡ b
not-is-involution true  = refl true
not-is-involution false = refl false
```

### Exercise 1 (★★)

Use pattern matching to **prove** that `||` is commutative.

```agda
||-is-commutative : (a b : Bool) → a || b ≡ b || a
||-is-commutative true true = refl true
||-is-commutative true false = refl true
||-is-commutative false true = refl true
||-is-commutative false false = refl false
```

### Exercise 2 (★★)

Taking inspiration from the above, try to **state** and **prove** that `&&` is
commutative.

```agda
&&-is-commutative : (a b : Bool) -> (a && b) ≡ (b && a)
&&-is-commutative true true = refl true
&&-is-commutative true false = refl false
&&-is-commutative false true = refl false
&&-is-commutative false false = refl false
```

### Exercise 3 (★★)

**Prove** that `&&` and `&&'` are both associative.

```agda
&&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
&&-is-associative true true c = refl c
&&-is-associative true false c = refl false
&&-is-associative false true c = refl false
&&-is-associative false false c = refl false

&&'-is-associative : (a b c : Bool) → a &&' (b &&' c) ≡ (a &&' b) &&' c
&&'-is-associative true true true = refl true
&&'-is-associative true true false = refl false
&&'-is-associative true false true = refl false
&&'-is-associative true false false = refl false
&&'-is-associative false true true = refl false
&&'-is-associative false true false = refl false
&&'-is-associative false false true = refl false
&&'-is-associative false false false = refl false
```

**Question**: Can you spot a downside of the more verbose definition of `&&'`
  now?

### Exercise 4 (★★★)

Another key feature of Agda is its ability to carry out inductive proofs. For
example, here is a commented inductive proof that `max` is commutative.

```agda
max-is-commutative : (n m : ℕ) → max n m ≡ max m n
max-is-commutative zero    zero    = refl zero
max-is-commutative zero    (suc m) = refl (suc m)
max-is-commutative (suc n) zero    = refl (suc n)
max-is-commutative (suc n) (suc m) = to-show
 where
  IH : max n m ≡ max m n      -- induction hypothesis
  IH = max-is-commutative n m -- recursive call on smaller arguments
  to-show : suc (max n m) ≡ suc (max m n)
  to-show = ap suc IH         -- ap(ply) suc on both sides of the equation
```

**Prove** analogously that `min` is commutative.

```agda
min-is-commutative : (n m : ℕ) → min n m ≡ min m n
min-is-commutative zero zero = refl 0
min-is-commutative zero (suc m) = refl 0
min-is-commutative (suc n) zero = refl 0
min-is-commutative (suc n) (suc m) = ap suc (min-is-commutative n m)
```

### Exercise 5 (★★★)

Using another inductive proof, **show** that `n ≡ n + 0` for every natural
number `n`.

```agda
0-right-neutral : (n : ℕ) → n ≡ n + 0
0-right-neutral zero = refl zero
0-right-neutral (suc n) = ap suc (0-right-neutral n)
```

### Exercise 6 (★★★)

The function `map` on lists is a so-called *functor*, which means that it
respects the identity and composition, as formally expressed below.

Try to **prove** these equations using pattern matching and inductive proofs.

```agda
map-id : {X : Type} (xs : List X) → map id xs ≡ xs
map-id [] = refl []
map-id (x :: xs) = ap (λ xs -> (x :: xs)) (map-id xs)

map-comp : {X Y Z : Type} (f : X → Y) (g : Y → Z)
           (xs : List X) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp f g [] = refl []
map-comp f g (x :: xs) = ap (λ xs -> ((g ∘ f) x) :: xs) (map-comp f g xs)
```
