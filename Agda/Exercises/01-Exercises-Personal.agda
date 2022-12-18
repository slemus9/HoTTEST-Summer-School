-- Personal solutions
module 01-Exercises-Personal where

open import prelude hiding (not-is-involution)


-- Part I: Writing functions on Booleans, natural numbers and lists (★/★★)

-- Exercise 1 (★)

_&&'_ : Bool → Bool → Bool
true  &&' true  = true
true  &&' false = false
false &&' true  = false
false &&' false = false

-- Exercise 2 (★)

_xor_ : Bool → Bool → Bool
true  xor true  = true
false xor false = true
_     xor _     = false 

-- Exercise 3 (★)

_^_ : ℕ → ℕ → ℕ
n ^ zero  = 1
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example = refl 81 -- refl 81 should fill the hole here

_! : ℕ → ℕ
zero  ! = 1
suc n ! = suc n * (n !)

!-example : 4 ! ≡ 24
!-example = refl 24 -- refl 24 should fill the hole here

-- Exercise 4 (★)

max : ℕ → ℕ → ℕ
max zero    m       = m
max (suc n) zero    = suc n
max (suc n) (suc m) = suc (max n m)

min : ℕ → ℕ → ℕ
min zero    m       = zero
min (suc n) zero    = zero
min (suc n) (suc m) = suc (min n m)

min-example : min 5 3 ≡ 3
min-example = refl 3 -- refl 3 should fill the hole here

-- Exercise 5 (★)

map : {X Y : Type} → (X → Y) → List X → List Y
map f []        = []
map f (x :: xs) = f x :: map f xs

map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl _ -- refl _ should fill the hole here

-- Exercise 6 (★★)

filter : {X : Type} (p : X → Bool) → List X → List X
filter p []        = []
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

is-non-zero : ℕ → Bool
is-non-zero zero    = false
is-non-zero (suc _) = true

filter-example : filter is-non-zero (4 :: 3 :: 0 :: 1 :: 0 :: []) ≡ 4 :: 3 :: 1 :: []
filter-example = refl _ -- refl _ should fill the hole here
