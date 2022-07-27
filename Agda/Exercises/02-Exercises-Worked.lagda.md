# Week 02 - Agda Exercises

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

module 02-Exercises-Worked where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f = λ ab → f (pr₁ ab) (pr₂ ab) 

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f = λ a b -> f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl ab) = (inl (pr₁ ab) , inl (pr₂ ab))
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] n = (λ a → n (inl a)) , (λ b → n (inr b))

{--
[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] = 
know how to map (a,b) to empty,
but don't know how to map just one of either a or b to empty
--}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f nb = nb ∘ f
{--
[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] nf b = 
can't get an A from this

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] = 
can't get an A from this
--}
[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] f a = λ b → f (a , b)
{--
[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] = 
can't get an element of a
--}

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] f = (λ a → pr₁ (f a)) , λ a → pr₂ (f a)
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne n3 = λ a → n3 (λ f → f a)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f nna = λ nb → nna (nb ∘ f)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f nna = λ nb → nna (λ a → f a nb)
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true  = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ true true p = id , id
bool-≡-char₁ false false p = id , id
```


### Exercise 3 (★★)

Using ex. 2, concldude that
```agda
true≢false : ¬ (true ≡ false)
true≢false = λ x → (pr₁ (bool-≡-char₁ true false x)) ⋆
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true eq = refl true
bool-≡-char₂ true false eq = 𝟘-elim (pr₁ eq ⋆)
bool-≡-char₂ false true eq = 𝟘-elim (pr₂ eq ⋆)
bool-≡-char₂ false false eq = refl false
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```
Prove that
```agda
d0 : {A : Type} → {x y : A} → x ≡ y → A
d0 {A} {x} {y} p = x

d1 : {A : Type} → {x y : A} → x ≡ y → A
d1 {A} {x} {y} p = y

∂ : {A : Type} → {x y : A} → x ≡ y → A × A
∂ {A} {x} {y} p = (x , y)

decide : {A : Type} → A ∔ ¬ A → Bool
decide (inl _) = true
decide (inr _) = false


{--
diagrefl : {A : Type} → {d : has-decidable-equality A} → {x : A} → decide (d x x) ≡ true
diagrefl {A} {d} {x} = --

getrefl : {A : Type} → {a a' : A} → (deceqpt : is-decidable (a ≡ a')) → a ≡ a' → decide (deceqpt) ≡ true
getrefl (inl _) _ = refl true
getrefl (inr a≢a') p = 𝟘-nondep-elim --
--}
-- note that in the following, we can't use deceq : has-decidable-equality A, which would be more natural. This is because we can't case split on it...as far as I can tell? or maybe we just need to apply an appropriate lambda to it...
ap-bool-≡-y : {A : Type} → {x y : A} → (dec : is-decidable (x ≡ y)) → x ≡ y → decide dec ≡ true
ap-bool-≡-y (inl _) _ = refl _
ap-bool-≡-y (inr x≢x) p = 𝟘-nondep-elim (x≢x p)

false≢true : ¬ (false ≡ true)
false≢true = true≢false ∘ _⁻¹

ap-y-≡-bool : {A : Type} → {x y : A} → (dec : is-decidable (x ≡ y)) → decide dec ≡ true → x ≡ y
ap-y-≡-bool (inl p) _ = p 
ap-y-≡-bool (inr _) false≡true = 𝟘-nondep-elim (false≢true false≡true)



-- (∀ x y → x ≡ y ⇔ (f x y) ≡ true)

{-- so after all, the technique was: back up to the thing everything is dependent on, and define a
function that starts with that (and then takes in any other info you need) --}

decide-via-indicator : {A : Type} (expr : Bool) → (A ⇔ expr ≡ true) → is-decidable A
decide-via-indicator true  (_ , f) = inl (f (refl true))
decide-via-indicator false (f , _) = inr (false≢true ∘ f)

decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
pr₁ (decidable-equality-char A) deceq =
 (λ a a' → decide (deceq a a')) , -- takes an inhabitant of a ≡ a' to true and an inhabitant of the negation to false
 (λ a a' → (ap-bool-≡-y (deceq a a'),  ap-y-≡-bool (deceq a a')))
pr₂ (decidable-equality-char A) (eqb , p2b) a a' = decide-via-indicator (eqb a a') (p2b a a')
{--
testtt : (yf : Bool) → ((λ y → yf ≡ y) yf)
testtt yf = if[ λ x → x ≡ yf ] yf then (if yf then (refl _) else (refl _)) else (refl _)
--}


{--
ok so we have to start with refl _ : (f a a') ≡ (f a a').
Then we have to something that gets us to <something> : true ≡ f a a' in the case where 

if[ λ x → x ≡ yf ] yf then (if yf then refl else ()) else (refl _)

are we trying to use bool ind when we should use path ind? ∶
--}
{-
if[_]_then_else_ : (P : Bool → Type) → (x : Bool) → P true → P false → P x
if[ P ] true then t else f = t
if[ P ] false then t else f = f

ite : (P : Bool → Type) → (x : Bool) → P true → P false → P x
ite P true t f = t
ite P false t f = f
-}

{--
we need something that simultaneously recognizes the expression f a a' to be true in one branch and inhabits f a a' ≡ true,
and in the other takes f a a' ≡ false. Can we do that?


if[ λ x → x ≡ f a a' ] (f a a') then (refl _) else (refl _)
--}


{--
  
   λ x → inchoice x
     if[ λ {true → a ≡ a'; false → ¬ a ≡ a' } ]
     if (f a a') then inl (pr₂ p2b (refl _)) else inr (pr₁ p2b)
     
   λ y → (
    if[ λ x → (f a a') ≡ x ] (f a a')
    then (


   then (inl (pr₂ (p2b a a') (refl true)))
   else {!(inr ({!!} ∘ (pr₁ (p2b a a'))))!}
  
   basically: use f to get true or false...but how do we get that "inside" the equivalence?
   one strategy: prove in each context that it is equal to itself and compose paths
   another: use bool-≡-char₁ to get a map, and map out of true via pr₂ , and let the result sort itself out 

   λ a a' → (pr₁ (p2b a a')

   bool-≡-char₁ (f a a') true 

   bool-as-type (f a a')

   
--}
{--
test : (x : Bool) → (p : x ≡ true) → ℕ ∔ 𝟘
test x = Bool-ind (\ x -> x ≡ true -> ℕ ∔ 𝟘) (\ _ -> inl 1) (\p -> inr (false≢true p)) x
--}
{-
test : (x : Bool) → (p : x ≡ true) → ℕ ∔ 𝟘
test x = (if[ (\ x' -> (x' ≡ true) -> ℕ ∔ 𝟘) ] x then (\ p' -> inl 1) else (λ p' -> inr (false≢true p')))

inchoicetype : Type → Type → Bool → Type
inchoicetype A B = λ {true → (A → A ∔ B); false → (B → A ∔ B)}

inchoice : {A B : Type} → (x : Bool) → (inchoicetype A B x)
inchoice {A} {B} x = (if[ inchoicetype A B{--(λ {true → (A → A ∔ B); false → (B → A ∔ B)})--} ] x then inl else inr)
-}
```
A personal exercise: show that 𝟘 is a (right) identity (up to equivalence) for ∔,
i.e. that A ∔ 𝟘 is equivalent to A.
```agda
𝟘-right-identity : {A : Type} → ((A ∔ 𝟘) ⇔ A)
pr₁ 𝟘-right-identity (inl x) = x
pr₂ 𝟘-right-identity x = inl x

𝟘-left-identity : {A : Type} → ((𝟘 ∔ A) ⇔ A)
pr₁ 𝟘-left-identity (inr x) = x
pr₂ 𝟘-left-identity x = inr x
```

 