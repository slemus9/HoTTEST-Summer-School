```agda
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

module W-types where

open import new-prelude

```
We'll define $W$-types with the using the syntax `_◂_` instead of `sup` for convenience.

```agda
data 𝕎 {n k : Level} (A : Set n) (B : A -> Set k) : Set (n ⊔ k) where
    _◂_ : (a : A) -> (f : B a -> 𝕎 A B) -> 𝕎 A B
```
We assume we've got the unit type, an empty type, Π and Σ types, and ∔. We'll take 𝟚 to be given by

```
𝟚 : Type
𝟚 = 𝟙 ∔ 𝟙
```

Then, take
```
ℕᵂ : Type
ℕᵂ = 𝕎 𝟚 λ { inl _ → 𝟘 ; inr _ → 𝟙}

