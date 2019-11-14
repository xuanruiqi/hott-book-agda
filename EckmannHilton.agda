{-# OPTIONS --without-K --exact-split --safe #-}
open import Agda.Primitive
open import Relation.Binary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

variable
  ℓ : Level
  A : Set ℓ

inv : ∀ {x y : A} → (x ≡ y) → y ≡ x
inv refl = refl

_·_ : ∀ {x y z : A} → (x ≡ y) → (y ≡ z) → x ≡ z
refl · refl = refl

𝟙ᵣ : ∀ {x y : A} {p : x ≡ y} → p ≡ p · refl
𝟙ᵣ {p = refl} = refl

𝟙ₗ : ∀ {x y : A} {p : x ≡ y} → p ≡ refl · p
𝟙ₗ {p = refl} = refl

variable
  a b c : A

_·ᵣ_ : ∀ {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → p · r ≡ q · r
α ·ᵣ refl = ((inv ru-p) · α) · ru-q
  where
    ru-p = 𝟙ᵣ
    ru-q = 𝟙ᵣ

_·ₗ_ : ∀ {r s : b ≡ c} → (q : a ≡ b) → (β : r ≡ s) → q · r ≡ q · s
refl ·ₗ β = ((inv luᵣ) · β) · luₛ
  where
    luᵣ = 𝟙ₗ
    luₛ = 𝟙ₗ

hor-comp : ∀ {p q : a ≡ b} {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
hor-comp {q = q} {r = r} α β = (α ·ᵣ r) · (q ·ₗ β)

_★_ : ∀ {p q : a ≡ b} {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
α ★ β = hor-comp α β
