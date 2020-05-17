{-# OPTIONS --without-K --exact-split --safe #-}

module Path where
  open import HUniverse
  open import Function using (id; _∘_)
  import Relation.Binary.PropositionalEquality as Eq
  open Eq public using (_≡_; refl)
  open Eq.≡-Reasoning public using (begin_; step-≡; _∎)
  open import Data.Product

  private
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

  Pointed : (ε : ULevel) → Type (lsucc ε)
  Pointed ε = Σ (Type ε) (λ A → A)

  -- record Pointed (ε : ULevel) : Type (lsucc ε) where
  --   constructor ●[_,_]
  --   field
  --     base : Type ε
  --     pt   : base

  -- open Pointed public

  -- _,_ : ∀ {ε : ULevel} → (A : Type ε) → A → Pointed ε
  -- A , a = ●[ A , a ]

  module Ap {ε : ULevel} {B : Type ε} where
    ap : ∀ {x y : A} (f : A → B) → (x ≡ y) → (f x ≡ f y)
    ap f refl = refl
  
    ap-· : ∀ {x y z : A} {f : A → B} {p : x ≡ y} {q : y ≡ z} → ap f (p · q) ≡ ap f p · ap f q
    ap-· {p = refl} {q = refl} = refl

    ap⁻¹ : ∀ {x y : A} {f : A → B} {p : x ≡ y} → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
    ap⁻¹ {p = refl} = refl

  open Ap public

  ap-comp : ∀ {ε φ : ULevel} {B : Type ε} {C : Type φ} {x y : A} {f : A → B} {g : B → C} {p : x ≡ y} → ap g (ap f p) ≡ ap (g ∘ f) p
  ap-comp {p = refl} = refl

  ap-id : ∀ {x y : A} → {p : x ≡ y} → ap (id {A = A}) p ≡ p
  ap-id {p = refl} = refl

  module Transport {ε : ULevel} where
    transport : ∀ {x y : A} (P : A → Type ε) → (p : x ≡ y) → (P x → P y)
    transport P refl = id

    syntax transport P p = p ⋆[ P ]

    lift : ∀ {x y : A} {P : A → Type ε} (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , (p ⋆[ P ]) u)
    lift u refl = refl

    -- lift-law : ∀ {x y : A} {P : A → Type ε} (u : P x) → (p : x ≡ y) → ap proj₁ (lift u p) ≡ p
    -- lift-law u p = {!!} 

    apd : ∀ {x y : A} {P : A → Type ε} (f : (x : A) → P x) → (p : x ≡ y) → ((p ⋆[ P ]) (f x)) ≡ (f y)
    apd f refl = refl

    transport-const : ∀ {x y : A} (B : Type ε) → (p : x ≡ y) → (b : B) → transport (λ _ → B) p b ≡ b
    transport-const B refl b = refl

    transport-const-lem : ∀ {x y : A} {B : Type ε} (f : A → B) → (p : x ≡ y) → apd f p ≡ (transport-const B p (f x)) · (ap f p)
    transport-const-lem f refl = refl

    transport-· : ∀ {x y z : A} {P : A → Type ε} → (p : x ≡ y) → (q : y ≡ z) → (u : P x) → transport P q (transport P p u) ≡ transport P (p · q) u
    transport-· refl refl u = refl

    transport-∘ : ∀ {x y : A} {B : Type ε} {P : B → Type ε} {f : A → B} → (p : x ≡ y) → (u : P (f x)) → transport (P ∘ f) p u ≡ transport P (ap f p) u
    transport-∘ refl u = refl

    transport-family : ∀ {x y : A} {P Q : A → Type ε} {f : ∀ (x : A) → P x → Q x} → (p : x ≡ y) → (u : P x) → transport Q p (f x u) ≡ f y (transport P p u)
    transport-family refl u = refl

  open Transport public
