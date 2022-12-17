{-
  --without-K: agda is inconsistent with HoTT. This flag makes it consistent. Why?
  --safe: for the soundness of the proofs (we can't use postulate for example)
-}
{-# OPTIONS --without-K --safe #-}

-- Personal notes
module plecture1 where

-- open import general-notation
{-
  Not all Types are Sets
-}
Type = Set

data Bool : Type where
  true false : Bool

not : Bool → Bool
not true  = false
not false = true

idBool : Bool → Bool
idBool x = x

{-
We can create holes for types and resolve them
using C-c C-s (solve constraints)
idBool' : Bool → Bool
idBool' = λ (x : ?) → x
-}
idBool' : Bool → Bool
idBool' = λ (x : Bool) → x

-- This is a Π type
id' : (X : Type) → X → X
id' X x = x

-- X is an implicit parameter
id : {X : Type} → X → X
id x = x

-- Agda infers the implicit parameter
idBool'' : Bool → Bool
idBool'' = id
-- idBool'' = id' Bool
-- idBool'' = id' _
-- idBool'' = id {Bool}

{-
  Propositions as types
  Mathematical statements as types
-}
example1 : {P Q : Type} → P → Q → P
example1 p _ = p

{-
  other definitions

example1 : {P Q : Type} → P → Q → P
example1 {P} {Q} p = f
  where
    f : P → Q
    f _ = p

example1 : {P Q : Type} → P → Q → P
example1 p = λ q → p
-}

open import binary-products

example2 : {P Q : Type} → P × Q → Q × P
example2 (p , q) = (q , p)

data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ 

_ : ℕ
_ = suc (suc (suc zero))

-- Tell agda to allow us to use number symbols for ℕ
{-# BUILTIN NATURAL ℕ #-}
_ : ℕ
_ = 3

-- Dependent type, also called a type family, is a function
D : Bool → Type
D true = ℕ
D false = Bool

-- mix-fix operator
if_then_else_ : {X : Type} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

if[_]_then_else_ : (X : Bool → Type)
                → (b : Bool) 
                → X true 
                → X false 
                → X b
if[ X ] true then x else y  = x
if[ X ] false then x else y = y

-- Π (b : Bool) . D b
unfamiliar : (b : Bool) → D b
unfamiliar b = if[ D ] b then 3 else false

-- List is a function from Type to Type
data List (A : Type) : Type where
  []   : List A -- empty
  _::_ : A → List A → List A -- cons

-- Infix operator, right associative, with precedence 10
infixr 10 _::_

ff : Type → Type
ff = List

_ : List ℕ
_ = 0 :: 1 :: 2 :: 3 :: []

{-
  In agda, recursive definition must terminate. The
  recursive call argument should be structurally smaller
  than the initial parameter

  In the Martin Löf type theory we don't have recursive
  definitions. We have elimination principles
-}
length : {X : Type} → List X → ℕ
length []        = 0
length (x :: xs) = suc (length xs)

{-
  Principle of induction on ℕ - Elimination principle
  This is the only recursive definition that we have in 
  Martin Löf's type theory. Every other recursive definition
  that we need can be expressed in terms of this one
-}
ℕ-elim : {A : ℕ → Type} -- Type family indexed by Natural Numbers
       → (A 0)
       → ((k : ℕ) → A k → A (suc k)) -- dependent function
       → (n : ℕ) → A n
-- Definitional equalities: 
ℕ-elim a0 f zero    = a0
ℕ-elim a0 f (suc n) = f n (ℕ-elim a0 f n)

List-elim : {X : Type} (A : List X → Type) -- Type family indexed by Lists
          → A []
          → ((x : X) (xs : List X) → A xs → A (x :: xs))
          → (xs : List X) → A xs
List-elim A a0 f []        = a0
List-elim A a0 f (x :: xs) = f x xs (List-elim A a0 f xs)

-- Equality of ℕ as a type . We use propositions as types again
-- Empty type corresponds to false
data 𝟘 : Type where -- \b0
  -- We cannot construct a term of type empty
  -- False has not proofs

-- Unit type corresponds to true
data 𝟙 : Type where -- \b1
  ⋆ : 𝟙 -- \star

_≣_ : ℕ → ℕ → Type
zero  ≣ zero  = 𝟙
zero  ≣ suc y = 𝟘
suc x ≣ zero  = 𝟘
suc x ≣ suc y = x ≣ y

infix 0 _≣_

ℕ-refl : (x : ℕ) → x ≣ x
ℕ-refl zero    = ⋆
ℕ-refl (suc x) = ℕ-refl x

-- Natural number addition
_+_ : ℕ → ℕ → ℕ
zero    + y = y
(suc x) + y = suc (x + y)

-- List concatenation
_++_ : {A : Type} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- length is a monoid homomorphism 
lh : {X : Type} (xs ys : List X)
   → length (xs ++ ys) ≣ length xs + length ys
lh []        ys = ℕ-refl (length ys)
{-
  Agda performs computations when we ask for the goal:
  (unfolding of definitions)

  length ((x :: xs) ++ ys) ≣ length (x :: xs) + length ys
= <length>
  length ((x :: xs) ++ ys) ≣ suc (length xs) + length ys
= <+>
  length ((x :: xs) ++ ys) ≣ suc (length xs + length ys)
= <++>
  length (x :: (xs ++ ys)) ≣ suc (length xs + length ys)
= <length>
  suc (length (xs ++ ys)) ≣ suc (length xs + length ys)
= <_≣_>
  length (xs ++ ys) ≣ length xs + length ys
-}
lh (x :: xs) ys = lh xs ys 