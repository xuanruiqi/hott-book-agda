{-# OPTIONS --without-K --exact-split --safe #-}
module Path where
  open import HUniverse
  import Relation.Binary.PropositionalEquality as Eq
  open Eq public using (_≡_; refl; cong)
  open Eq.≡-Reasoning public using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

  variable
    ℓ : ULevel
    A : Type ℓ

  _⁻¹ : ∀ {x y : A} → (x ≡ y) → y ≡ x
  refl ⁻¹ = refl

  _·_ : ∀ {x y z : A} → (x ≡ y) → (y ≡ z) → x ≡ z
  refl · refl = refl

  𝟙ᵣ : ∀ {x y : A} {p : x ≡ y} → p ≡ p · refl
  𝟙ᵣ {p = refl} = refl
  
  𝟙ₗ : ∀ {x y : A} {p : x ≡ y} → p ≡ refl · p
  𝟙ₗ {p = refl} = refl

  inv-cancelₗ : ∀ {x y : A} {p : x ≡ y} → (p ⁻¹) · p ≡ refl
  inv-cancelₗ {p = refl} = refl

  inv-cancelᵣ : ∀ {x y : A} {p : x ≡ y} → p · (p ⁻¹) ≡ refl
  inv-cancelᵣ {p = refl} = refl

  inv-invo : ∀ {x y : A} {p : x ≡ y} → (p ⁻¹) ⁻¹ ≡ p
  inv-invo {p = refl} = refl

  ·-assoc : ∀ {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} → (p · q) · r ≡ p · (q · r)
  ·-assoc {p = refl} {q = refl} {r = refl} = refl
