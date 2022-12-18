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

-- Part II: The identity type of the Booleans (★/★★)

-- Exercise 1 (★)

_≣_ : Bool → Bool → Type
true  ≣ true  = 𝟙
false ≣ false = 𝟙
_     ≣ _     = 𝟘

-- Exercise 2 (★)

Bool-refl : (b : Bool) → b ≣ b
Bool-refl true  = ⋆
Bool-refl false = ⋆

-- Exercise 3 (★★)

≡-to-≣ : (a b : Bool) → a ≡ b → a ≣ b
≡-to-≣ true  _ (refl _) = ⋆
≡-to-≣ false _ (refl _) = ⋆

≣-to-≡ : (a b : Bool) → a ≣ b → a ≡ b
≣-to-≡ true  true  ★ = refl true
≣-to-≡ false false _ = refl false

-- Part III: Proving in Agda (★★/★★★)

not-is-involution : (b : Bool) → not (not b) ≡ b
not-is-involution true  = refl true
not-is-involution false = refl false

-- Exercise 1 (★★)

||-is-commutative : (a b : Bool) → a || b ≡ b || a
||-is-commutative true  true  = refl true
||-is-commutative true  false = refl true
||-is-commutative false true  = refl true
||-is-commutative false false = refl false

-- Exercise 2 (★★)

&&-is-commutative : (a b : Bool) → a && b ≡ b && a
&&-is-commutative true  true  = refl true
&&-is-commutative true  false = refl false
&&-is-commutative false true  = refl false
&&-is-commutative false false = refl false

-- Exercise 3 (★★)

&&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
&&-is-associative true  b c = refl (b && c) 
&&-is-associative false b c = refl false

{-
  With the &&' definition we have to enumerate all possible cases
-}
&&'-is-associative : (a b c : Bool) → a &&' (b &&' c) ≡ (a &&' b) &&' c
&&'-is-associative true true true = refl true
&&'-is-associative true true false = refl false
&&'-is-associative true false true = refl false
&&'-is-associative true false false = refl false
&&'-is-associative false true true = refl false
&&'-is-associative false true false = refl false
&&'-is-associative false false true = refl false
&&'-is-associative false false false = refl false

-- Exercise 4 (★★★)

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

min-is-commutative : (n m : ℕ) → min n m ≡ min m n
min-is-commutative zero zero = refl zero
min-is-commutative zero (suc m) = refl zero
min-is-commutative (suc n) zero = refl zero
min-is-commutative (suc n) (suc m) = ap suc (min-is-commutative n m)

-- Exercise 5 (★★★)

0-right-neutral : (n : ℕ) → n ≡ n + 0
0-right-neutral zero    = refl zero
0-right-neutral (suc n) = ap suc (0-right-neutral n)

-- Exercise 6 (★★★)

map-id : {X : Type} (xs : List X) → map id xs ≡ xs
map-id []        = refl []
map-id (x :: xs) = ap (x ::_) (map-id xs)

map-comp : {X Y Z : Type} (f : X → Y) (g : Y → Z)
           (xs : List X) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp f g [] = refl []
map-comp f g (x :: xs) = ap ((g ∘ f) x ::_) (map-comp f g xs)
