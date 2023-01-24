{-# OPTIONS --without-K --safe #-}

module plecture2 where

open import lecture1 hiding (𝟘 ; 𝟙 ; D ; ℕ ; _+_)

data 𝟘 : Type where

-- 𝟘 is interpreted as false
𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()

¬_ : Type → Type
¬_ A = A → 𝟘

infix 1000 ¬_ 

𝟘-nondep-elim : {B : Type} → 𝟘 → B 
𝟘-nondep-elim {B} = 𝟘-elim {λ _ → B}

is-empty : Type → Type
is-empty = ¬_ 

𝟘-is-empty : is-empty 𝟘 
𝟘-is-empty = id

record 𝟙 : Type where 
  constructor
    ★

open 𝟙 public 

𝟙-is-nonempty : ¬ is-empty 𝟙   
𝟙-is-nonempty not𝟙 = not𝟙 ★

𝟙-elim : {A : 𝟙 → Type}
  → A ★
  → (x : 𝟙) → A x
𝟙-elim a ★ = a

-- Data type isomorphic to the booleans
data 𝟚 : Type where
  false true : 𝟚 

𝟚-elim : {A : 𝟚 → Type}
  → A false
  → A true
  → (x : 𝟚) → A x
𝟚-elim x1 _ false = x1
𝟚-elim _ x2 true  = x2

-- This is an if-then-else
𝟚-nondep-elim : {A : Type}
  → A 
  → A 
  → 𝟚 → A
𝟚-nondep-elim {A} = 𝟚-elim {λ _ → A}

-- Pi Syntax
Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

syntax Pi A (λ x → b) = Π x of A , b 

module _ where
  private
    _∘_ : {A B C : Type} → (B → C) → (A → B) → A → C
    (g ∘ f) x = g (f x)

-- A more general version 
-- Interpret this with propositions as types
_∘_ : {A B : Type} {C : B → Type}
  → (∀ b → C b)
  → (f : A → B)
  → (∀ a → C (f a))
(g ∘ f) x = g (f x)

