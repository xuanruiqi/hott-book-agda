{-# OPTIONS --without-K --exact-split --safe #-}

-- Agda proof of the Eckmann-Hilton theorem, following 2.1.6 in the HoTT Book

module EckmannHilton where
  open import HUniverse
  open import Path

  variable
    ℓ : ULevel

  Ω[_,_] : (A : Type ℓ) → (a : A) → Type ℓ
  Ω[ A , a ] = a ≡ a
  
  Ω²[_,_] : (A : Type ℓ) → (a : A) → Type ℓ
  Ω²[ A , a ] = Ω[ (Ω[ A , a ]) , refl ]

  variable
    A : Type ℓ

  -- Whiskering
  _·ᵣ_ : ∀ {a b c : A} {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → p · r ≡ q · r
  α ·ᵣ refl = ((𝟙ᵣ ⁻¹) · α) · 𝟙ᵣ

  _·ₗ_ : ∀ {a b c : A} {r s : b ≡ c} → (q : a ≡ b) → (β : r ≡ s) → q · r ≡ q · s
  refl ·ₗ β = ((𝟙ₗ ⁻¹) · β) · 𝟙ₗ

  horizontal-comp : ∀ {a b c : A} {p q : a ≡ b} {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
  horizontal-comp {q = q} {r = r} α β = (α ·ᵣ r) · (q ·ₗ β)

  _★_ : ∀ {a b c : A} {p q : a ≡ b} {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
  α ★ β = horizontal-comp α β

  horizontal-comp' : ∀ {a b c : A} {p q : a ≡ b} {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
  horizontal-comp' {p = p} {s = s} α β = (p ·ₗ β) · (α ·ᵣ s)

  _★'_ : ∀ {a b c : A} {p q : a ≡ b} {r s : b ≡ c} → (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
  α ★' β = horizontal-comp' α β

  ★-★'-equiv : ∀ {a : A} {p : a ≡ a} {r : a ≡ a} → (α : p ≡ refl) → (β : r ≡ refl) → α ★ β ≡ α ★' β
  ★-★'-equiv refl refl = refl

  ★-·-equiv : ∀ {a : A} (α β : Ω²[ A , a ]) → α ★ β ≡ α · β
  ★-·-equiv α β =
    begin
      α ★ β
    ≡⟨ refl ⟩
      (((𝟙ᵣ ⁻¹) · α) · 𝟙ᵣ) · (((𝟙ₗ ⁻¹) · β) · 𝟙ₗ)
    ≡⟨ refl ⟩
      (((refl ⁻¹) · α) · refl) · (((refl ⁻¹) · β) · refl)  
    ≡⟨ refl ⟩
      ((refl · α) · refl) · ((refl · β) · refl)
    ≡⟨ ap (λ m → (m · _) · _) (𝟙ₗ ⁻¹) ⟩
      (α · refl) · ((refl · β) · refl)
    ≡⟨ ap (λ m → _ · (m · _)) (𝟙ₗ ⁻¹) ⟩
      (α · refl) · (β · refl)
    ≡⟨ ap (λ m → m · _) (𝟙ᵣ ⁻¹) ⟩
      α · (β · refl)
    ≡⟨ ap (λ m → _ · m) (𝟙ᵣ ⁻¹) ⟩
      α · β
    ∎

  ★'-·-equiv : ∀ {a : A} (α β : Ω²[ A , a ]) → α ★' β ≡ β · α
  ★'-·-equiv α β =
    begin
      α ★' β
    ≡⟨ refl ⟩
      (((𝟙ₗ ⁻¹) · β) · 𝟙ₗ) · (((𝟙ᵣ ⁻¹) · α) · 𝟙ᵣ)
    ≡⟨ refl ⟩
      (((refl ⁻¹) · β) · refl) · (((refl ⁻¹) · α) · refl)
    ≡⟨ refl ⟩
      ((refl · β) · refl) · ((refl · α) · refl)
    ≡⟨ ap (λ m → (m · _) · _) (𝟙ₗ ⁻¹) ⟩
      (β · refl) · ((refl · α) · refl)
    ≡⟨ ap (λ m → _ · (m · _))(𝟙ₗ ⁻¹) ⟩
      (β · refl) · (α · refl)
    ≡⟨ ap (λ m → m · _) (𝟙ᵣ ⁻¹) ⟩
      β · (α · refl)
    ≡⟨ ap (λ m → _ · m) (𝟙ᵣ ⁻¹) ⟩
      β · α
    ∎

  eckmann-hilton : ∀ {a : A} (α β : Ω²[ A , a ]) → α · β ≡ β · α
  eckmann-hilton α β =
    begin
      α · β
    ≡⟨ (★-·-equiv α β) ⁻¹ ⟩
      α ★ β
    ≡⟨ ★-★'-equiv α β ⟩
      α ★' β
    ≡⟨ ★'-·-equiv α β ⟩
      β · α
    ∎
