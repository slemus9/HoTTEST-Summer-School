```agda
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

module W-types where

open import copied-prelude
open import binary-sums
open import empty-type

```
### 🏗 Under construction 🚧

We'll define $W$-types with the using the syntax `_◂_` instead of `sup` for convenience. In the following, we follow the construction described in [*Why not W?*](https://jashug.github.io/papers/whynotw.pdf) by Jasper Hugunin.

```agda
data 𝕎 {n k : Level} (A : Set n) (B : A -> Set k) : Set (n ⊔ k) where
    _◂_ : (a : A) -> (f : B a -> 𝕎 A B) -> 𝕎 A B

infix 1 _◂_

syntax 𝕎 A (λ x → B) = 𝕎 x ꞉ A , B
```
We assume we've got the unit type, an empty type, Π and Σ types, and ∔. We'll take 𝟚 to be given by
```
data 𝟚 : Type where
 𝟎 : 𝟚
 𝟏 : 𝟚
```
Then, take
```
ℕᵂ' : Type
ℕᵂ' = 𝕎 𝟚 λ { 𝟎 → 𝟘 ; 𝟏 → 𝟙}

𝟘! : {A : Type} → 𝟘 → A
𝟘! ()

canonical : ℕᵂ' → Type
canonical (𝟎 ◂ f) = f ≡ 𝟘!
canonical (𝟏 ◂ f) = canonical (f ⋆)

ℕᵂ : Type
ℕᵂ = Σ canonical

zeroᵂ : ℕᵂ
zeroᵂ = (𝟎 ◂ 𝟘! , refl _)

sucᵂ : ℕᵂ → ℕᵂ
sucᵂ (n , c) = (𝟏 ◂ (λ {⋆ → n}), c)
```
For the induction principle, the paper suggests we do path induction directly on `c`. However:
```agda
indℕᵂ : (P : ℕᵂ → Type) → P zeroᵂ → ((n : ℕᵂ) → P n → P (sucᵂ n)) → (m : ℕᵂ) → P m
indℕᵂ P p0 ps (𝟎 ◂ f , (refl _)) = p0
indℕᵂ P p0 ps (𝟏 ◂ f , c) = ps (f ⋆ , c) (indℕᵂ P p0 ps (f ⋆ , c))
```
To get the induction principle, we could also have made explicit use of the homotopy between any pair $(a , c) : \Sigma_{a : A} (a = \text{canon})$ and the pair $(\text{canon}, \text{refl}_\text{canon})$ given by shrinking along the given path $c$. (This is essentially the fact that $\text{isContr}(A)$ is a proposition.) This is immediate from path induction.
```agda
shrink : {A : Type} (canon : A) (a : A) (c : a ≡ canon) →
         ((canon , refl canon) ≡ (a , c))
shrink _ _ (refl _) = refl _
```
We then use this to transport within a type family over those pairs:
```agda
transportshrink : {A : Type} {canon : A} →
                  (Q : (Σ λ a' → (a' ≡ canon)) → Type) →
                  (a : A) → (c : a ≡ canon) →
                  Q (canon , (refl canon)) → Q (a , c)
transportshrink {canon = canon} Q a c = transport Q (shrink canon a c)
```
By considering the type family given by abstracting over pairs of `f` and `c` in `P ((𝟎 ◂ f) , c)`, we can just (un)shrink from the proof for the canonical element to a proof for our given element. (Maybe I should rename my lemmas.)
```agda
indℕᵂ' : (P : ℕᵂ → Type) → P zeroᵂ → ((n : ℕᵂ) → P n → P (sucᵂ n)) → (m : ℕᵂ) → P m
indℕᵂ' P p0 ps (𝟎 ◂ f , c) = transportshrink
                                (λ (ff , cc) → P (𝟎 ◂ ff , cc))
                                f c p0
indℕᵂ' P p0 ps (𝟏 ◂ f , c) = ps (f ⋆ , c) (indℕᵂ' P p0 ps (f ⋆ , c))
```
Are these the same? I expect the path induction for `shrink` is essentially "the same" as the path induction for `indℕᵂ'` at the top level, but I'm not sure. They aren't judgmentally equal, of course:
```agda
same : (P : ℕᵂ → Type) → (p0 : P zeroᵂ) → (ps : (n : ℕᵂ) → P n → P (sucᵂ n)) → (f : 𝟘 → ℕᵂ') → (c : canonical (𝟎 ◂ f)) → indℕᵂ P p0 ps (𝟎 ◂ f , c) ≡ indℕᵂ' P p0 ps (𝟎 ◂ f , c)
same P p0 ps f c = {!!} --cannot be filled by refl _
```
In any case, does this have the right computational behavior? Let's test it out. We define a couple "canonical" numbers:
```agda
one two three : ℕᵂ
one = sucᵂ zeroᵂ
two = sucᵂ one
three = sucᵂ two
```
We define addition *without* induction, in the following manner:
```agda
addᵂ : ℕᵂ → ℕᵂ → ℕᵂ
addᵂ (𝟎 ◂ f , c) x = x
addᵂ (𝟏 ◂ f , c) x = sucᵂ (addᵂ (f ⋆ , c) x)
```
Let's test it out on our canonical numbers:
```agda
four₁ᵂ four₂ᵂ : ℕᵂ
four₁ᵂ = addᵂ two two
four₂ᵂ = addᵂ one three

eq4ᵂ : four₁ᵂ ≡ four₂ᵂ
eq4ᵂ = refl _
```
[*Is the following section showing anything interesting? Keep?*]

Do we get the same thing if we use our new natural number induction?
```agda
add : ℕᵂ → ℕᵂ → ℕᵂ
add = indℕᵂ (λ _ → (ℕᵂ → ℕᵂ)) (λ x → x) (λ _ f → sucᵂ ∘ f)

four₁ four₂ : ℕᵂ
four₁ = add two two
four₂ = add one three

eq4 : four₁ ≡ four₂
eq4 = refl _

eq4-ᵂ : four₁ᵂ ≡ four₁
eq4-ᵂ = refl _
```
What if we use the *other* induction?
```agda
add' : ℕᵂ → ℕᵂ → ℕᵂ
add' = indℕᵂ' (λ _ → (ℕᵂ → ℕᵂ)) (λ x → x) (λ _ f → sucᵂ ∘ f)

four₁' four₂' : ℕᵂ
four₁' = add two two
four₂' = add one three

eq4' : four₁' ≡ four₂'
eq4' = refl _

eq4-' : four₁ ≡ four₁'
eq4-' = refl _

eq4'ᵂ : four₁' ≡ four₁ᵂ
eq4'ᵂ = refl _
```
Yes! ...At least on these canonical numbers. But what about *non*canonical numbers? Do we need to worry about such a thing? Well, let's assume another 0.
```agda
𝟘!' : {A : Type} → 𝟘 → A
𝟘!' x = 𝟘-nondep-elim x

postulate
 eq𝟘! : {A : Type} → 𝟘!' {A} ≡ 𝟘! {A}

zeroᵂ' : ℕᵂ
zeroᵂ' = 𝟎 ◂ 𝟘!' , eq𝟘!

one' : ℕᵂ
one' = sucᵂ zeroᵂ'

eq1 : one ≡ one'
eq1 = ap (λ (f , c) → sucᵂ (𝟎 ◂ f , c)) (shrink 𝟘! 𝟘!' eq𝟘!)
```
So there *is* a path, but it's not refl; it comes from wherever our path to the canonical element came from. That makes sense. As stated in the paper, we lose canonicity for our natural numbers if we lose canonicty for the relevant identity types.

I wonder where we *do* actually need computation on the naturals on noncanonical elements. Maybe I should try to prove that $0 + x = x$. Actually, let's just try to get an equivalence.
```
data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

open _≅_ public
open is-bijection public

ℕ≅ℕᵂ : ℕ ≅ ℕᵂ
bijection ℕ≅ℕᵂ = f -- forced to use a where clause here because of insufficient termination checking
 where
  f : ℕ → ℕᵂ
  f = λ { zero → zeroᵂ ; (suc n) → sucᵂ (f n) }
inverse (bijectivity ℕ≅ℕᵂ) = g
 where
  g : ℕᵂ → ℕ
  g (𝟎 ◂ _ , _) = zero
  g (𝟏 ◂ f , c) = suc (g (f ⋆ , c))
η (bijectivity ℕ≅ℕᵂ) = eta
 where
  eta : (inverse (bijectivity ℕ≅ℕᵂ) ∘ bijection ℕ≅ℕᵂ) ∼ id
  eta zero = refl _
  eta (suc x) = ap suc (eta x)
ε (bijectivity ℕ≅ℕᵂ) = eps
 where
  eps : (bijection ℕ≅ℕᵂ ∘ inverse (bijectivity ℕ≅ℕᵂ)) ∼ id
  eps (𝟎 ◂ f , refl _) = refl _ -- could also use c instead of refl and proceed via shrink
  eps (𝟏 ◂ f , c) = ap sucᵂ (eps (f ⋆ , c))
```
Yay!
```agda
data bottomlessℕ : Type where
 suc? : bottomlessℕ → bottomlessℕ

data ℤ : Type where
 zero : ℤ
 next : ℤ → ℤ

data Sign : Type where
 [0] [-] [+] : Sign

sign : ℤ → Sign
sign zero = [0]
sign (next zero) = [-]
sign (next (next zero)) = [+]
sign (next (next (next n))) = sign (next n)

sucℤ : ℤ → ℤ
sucℤ = {!!}
```

[*To do: implement the remainder of the paper; break up into sections*]






 