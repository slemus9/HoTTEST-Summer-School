# 🏗 Under construction 🚧

There are a bunch of cool definitions of the integers that take advantage of HoTT, such as defining them as the loop space of the circle; there are also a bunch of cool definitions that come about after formalizing algebra in agda, such as taking the integers to be the free group on one generator.

We won't be exploring those here (yet). This is just a way to explore different "mechanistic" characterizations of the integers...and maybe a way to do something else. We'll see.

We'll keep things consistent with HoTT just in case.
```agda
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

module The-Integers where

open import copied-prelude
open import Lecture5-notes
```
The first idea here is that one definition of the integers is just...the naturals. It all depends on how you work with them! If your operations treat them as the integers, they may as well be the integers.
```agda
data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data ℤ : Type where
 zero : ℤ
 next : ℤ → ℤ
```
We'll find it convenient to talk about the sign of an integer.
```agda
data Sign : Type where
 [0] [-] [+] : Sign

- : Sign → Sign
- [0] = [0]
- [-] = [+]
- [+] = [-]

_*_ : Sign → Sign → Sign
[+] * σ = σ
[-] * σ = - σ
[0] * _ = [0]
```
We take odd naturals to be negative and even naturals to be positive.
```agda
sign : ℤ → Sign
sign zero = [0]
sign (next zero) = [-]
sign (next (next zero)) = [+]
sign (next (next (next n))) = sign (next n)

absℤ : ℤ → ℕ
absℤ zero = 0
absℤ (next zero) = suc 0
absℤ (next (next n)) = suc (absℤ n)

unnext : ℤ → ℤ
unnext zero = zero
unnext (next n) = n

sucℤ : ℤ → ℤ
sucℤ n with sign n
...         | [0] = next (next zero)
...         | [+] = next (next n)
...         | [-] = unnext (unnext n)

preℤ : ℤ → ℤ
preℤ n with sign n
...         | [0] = (next zero)
...         | [+] = unnext (unnext n)
...         | [-] = next (next n)



_∘^_ : {X : Type} → (X → X) → ℕ → (X → X)
f ∘^ 0 = id
f ∘^ (suc n) = λ x → (f ∘^ n) (f x)

addℤ : ℤ → ℤ → ℤ
addℤ n with sign n
...         | [0] = id
...         | [+] = sucℤ ∘^ (absℤ n)
...         | [-] = preℤ ∘^ (absℤ n)
```
Let's make another $\mathbb{Z}$. One drawback, computationally, is that to know whether an integer is positive or negative, we have to totally deconstruct it.

In the following, we can immediately determine the sign: the outermost constructor tells us if we're on the right or left.
```agda
data ℤ' : Type where
 zero : ℤ'
 r : ℤ' → ℤ'
 l : ℤ' → ℤ'

sign' : ℤ' → Sign
sign' zero = [0]
sign' (r _) = [+]
sign' (l _) = [-]
```
Now we just need a nice way to assign all bitstrings of a certain length to magnitudes. Well, there's binary! And it turns out to lend itself quite easily to the integers. Let's define a function called "out" which incrases the magnitude of nonzero functions by 1, and leaves 0 alone:
```agda
out : ℤ' → ℤ'
out zero = zero
out (r zero) = r (r zero)
out (l zero) = l (l zero)
out (r (r n)) = r (l n)
out (l (l n)) = l (r n)
out (r (l n)) = r (out (r n))
out (l (r n)) = l (out (l n))

{-
out : ℤ' → ℤ'
out zero = zero
out (rl m) with sign' m
...          | [0] = rl

outhelp : LR → ℤ' → ℤ'
outhelp v x with sign' x
...            | [0] = ▹ v zero
...            | [-]
-}
```
Note that the definitions for the constructors are symmetric. We might expect, actually, that we can phrase this in a cleaner way.

Some things are a bit difficult in agda; we can't easily iterate over just r and l, as far as I know. It's hard to e.g. match on a pattern that's more generic than an explicit one: e.g., instead of writing l or r, we might wish to write a generic pattern x that matches either of them, and then "flip" it to the other one. In some cases, *you* know that something is true—e.g. that if we have any constructor other than zero, then the sign is [-] or [+]—but agda doesn't. All of this is a little outside of the kind of manipualtions permitted by agda. But we can hack it so that we can do the next best thing:
```agda
data LR : Type where
 L R : LR

▿ : LR → ℤ' → ℤ'
▿ L = l
▿ R = r

!! : LR → LR
!! L = R
!! R = L

signLR : LR → Sign
signLR L = [-]
signLR R = [+]

flip : ℤ' → ℤ'
flip zero = zero
flip (l m) = r m
flip (r m) = l m

incLR : (ℤ' → ℤ') → LR → ℤ' → ℤ'
incLR o d m with (signLR d) * (sign' m)
...            | [0] = ▿ d zero
...            | [+] = flip m
...            | [-] = o (flip m)

--The following would work...if termination checking didn't fail.
--I wish there were a way to prove to agda that it's fine.
{-
out' : ℤ' → ℤ'
out' zero = zero
out' (l m) = l (incLR out' L m)
out' (r m) = r (incLR out' R m)
-}
```
In any case, you can see that we still had to case split. This could maybe be remedied by using Sign instead of LR, and simply using inc out' (sign' n) n. We might also want to use zeroQ or something:
```agda
zeroQ : ℤ' → Bool
zeroQ zero = true
zeroQ _    = false
```
Or even better, map `[0]` to `id`:
```agda
▻ : Sign → ℤ' → ℤ'
▻ [0] = id
▻ [+] = r
▻ [-] = l

unwrap : ℤ' → ℤ'
unwrap zero = zero
unwrap (l n) = n
unwrap (r n) = n

inc : (ℤ' → ℤ') → Sign → ℤ' → ℤ'
inc o d m with d * (sign' m)
...          | [0] = ▻ d zero
...          | [+] = flip m
...          | [-] = o (flip m)

{-
out'' : ℤ' → ℤ'
out'' n = ▻ (sign' n) (inc out'' (sign' n) (unwrap n))
-}
```
The inverse of `out` is surprisingly hard to define recursively with reference only to itself. Instead, let's define "move". It takes in a sign denoting the direction of the movement
```agda
move : Sign → ℤ' → ℤ'
move [0] = id
move _ n = {!!}
{-
move-inner : Sign → Sign → ℤ' → ℤ'
move-inner dir sgn zero = ▻ dir zero
move-inner dir sgn rl0@(_ zero) with dir * (sign' rl0)
...                          | [0] = rl0
...                          | [+] = ▻ (sign' rl0) rl0
...                          | [-] = zero
move-inner dir sgn rln@(rl1@ (rl2@ n)) = {!!}
-}

```

Compare to the (outer) binary implementation of the naturals:
```agda
data B₂ : Type where
 b₀ b₁ : B₂

data bℕ⁺ : Type where
 [b₁] : bℕ⁺
 _▹_  : B₂ → bℕ⁺ → bℕ⁺

infixr 1 _▹_

sucbℕ⁺ : bℕ⁺ → bℕ⁺
sucbℕ⁺ [b₁] = b₀ ▹ [b₁]
sucbℕ⁺ (b₀ ▹ n) = b₁ ▹ n
sucbℕ⁺ (b₁ ▹ n) = b₁ ▹ b₀ ▹ n
```
But conceptually, these are actually the *whole* numbers! Sure, we could just declare everything to be shifted by 1; but under the obvious interpretation, we don't have 0. We'd need to essentially disjoint-sum with the one-point type. Using another copy of it can also get us the integers, like so:
```
data bℕ : Type where
 ◾[b₀] : bℕ
 ◾_    : bℕ⁺ → bℕ


sucbℕ : bℕ → bℕ
sucbℕ ◾[b₀] = ◾ [b₁]
sucbℕ (◾ n) = ◾ (sucbℕ⁺ n)


► : B₂ → bℕ → bℕ
(► b₀) ◾[b₀] = ◾[b₀]
(► b₁) ◾[b₀] = ◾ [b₁]
(► b) (◾ [b₁]) = ◾ (b ▹ [b₁])
(► b) (◾ (b' ▹ n)) = ◾ (b ▹ b' ▹ n)

prebℕ⁺ : bℕ⁺ → bℕ
prebℕ⁺ [b₁] = ◾[b₀]
prebℕ⁺ (b₁ ▹ n) = ◾ (b₀ ▹ n)
prebℕ⁺ (b₀ ▹ [b₁]) = ◾ [b₁]
prebℕ⁺ (b₀ ▹ n@(_ ▹ _)) = (► b₁) (prebℕ⁺ n)


data bℤ : Type where
 [b₀] : bℤ
 ⊞_ : bℕ⁺ → bℤ
 ⊟_ : bℕ⁺ → bℤ

bℤ-<bℕ : bℕ → bℤ
bℤ-<bℕ ◾[b₀] = [b₀]
bℤ-<bℕ (◾ x) = ⊞ x

negbℤ : bℤ → bℤ
negbℤ [b₀] = [b₀]
negbℤ (⊞ x) = ⊟ x
negbℤ (⊟ x) = ⊞ x



sucbℤ : bℤ → bℤ
sucbℤ [b₀]  = ⊞ [b₁]
sucbℤ (⊞ n) = ⊞ (sucbℕ⁺ n)
sucbℤ (⊟ n) = negbℤ (bℤ-<bℕ (prebℕ⁺ n))
 -- how do we use a function that's only defined for some patterns? we can't exactly use ∔ in general...do we have to inline it? That feels wrong...why can't we have partially-defined functions? Maybe what we actually need is bℕ>-bℤ here. Then we don't even have to case split: just apply predℕ⁺ and inject it. And I guess one for positive and one for negative? Or just apply a negation function after doing it.
```

So what if we added 0, and allowed either of the digits to be the "first" digit? Well, we'd need to establish a way to "collapse" a string of zeros down to zero...which is 
```agda
postulate
 Bℕ : Type
 [_] : B₂ → Bℕ
 _▸_ : B₂ → Bℕ → Bℕ
 mseg : (b : B₂) → b ▸ [ b₀ ] ≡ [ b ] -- accounts for all other equalities via ap
 Bℕ-elim : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : (b : B₂) → tree [ b₀ ] (base b₀) b ≡ base b [ P ↓ (mseg b) ]) →
           ((n : Bℕ) → P n)

 Bℕ-comp-[] : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : (b : B₂) → tree [ b₀ ] (base b₀) b ≡ base b [ P ↓ (mseg b) ]) →
           ((b : B₂) → Bℕ-elim P base tree path [ b ] ≡ base b)
      
 Bℕ-comp-▸ : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : (b : B₂) → tree [ b₀ ] (base b₀) b ≡ base b [ P ↓ (mseg b) ])
           (n : Bℕ) (b : B₂) →
            Bℕ-elim P base tree path (b ▸ n)
             ≡ tree n (Bℕ-elim P base tree path n) b

{-# REWRITE Bℕ-comp-[] #-}
{-# REWRITE Bℕ-comp-▸  #-}

postulate
 Bℕ-comp-mseg : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : (b : B₂) → tree [ b₀ ] (base b₀) b ≡ base b [ P ↓ (mseg b) ]) →
           (b : B₂) →
           apd (Bℕ-elim P base tree path) (mseg b) ≡ path b
```
Now it's time to show an equivalence! [Eventually.]

Now that we have the naturals (again), we can use many of the existing ways to turn the naturals into the integers. But what about doing it "natively"?

Let's define an essentially similar binary implementation of the integers. We'll through a "negate" operation into the mix: ⊟.

You might be saying, "this is unnecessarily complicated." And you're right! But we will do it anyway.

We also ideally want to define "the kind of thing that can have an inversion action performed on it."
```agda
{-
postulate
 Bℤ : Type
 [_] : B₂ → Bℤ
 _▸_ : B₂ → Bℤ → Bℤ
 ⊟   : Bℤ → Bℤ
 mseg : b₀ ▸ [ b₀ ] ≡ [ b₀ ] -- accounts for all other equalities via ap
 Bℕ-elim : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : tree [ b₀ ] (base b₀) b₀ ≡ base b₀ [ P ↓ mseg ]) →
           ((n : Bℕ) → P n)

 Bℕ-comp-[] : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : tree [ b₀ ] (base b₀) b₀ ≡ base b₀ [ P ↓ mseg ]) →
           ((b : B₂) → Bℕ-elim P base tree path [ b ] ≡ base b)
      
 Bℕ-comp-▸ : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : tree [ b₀ ] (base b₀) b₀ ≡ base b₀ [ P ↓ mseg ])
           (n : Bℕ) (b : B₂) →
            Bℕ-elim P base tree path (b ▸ n)
             ≡ tree n (Bℕ-elim P base tree path n) b

{-# REWRITE Bℕ-comp-[] #-}
{-# REWRITE Bℕ-comp-▸  #-}

postulate
 Bℕ-comp-mseg : (P : Bℕ → Type) →
           (base : (b : B₂) → P [ b ])
           (tree : (n : Bℕ) → P n → (b : B₂) → P (b ▸ n))
           (path : tree [ b₀ ] (base b₀) b₀ ≡ base b₀ [ P ↓ mseg ]) →
           apd (Bℕ-elim P base tree path) mseg ≡ path
-}
```
           












  