{-# OPTIONS --without-K --exact-split --safe #-}
module HUniverse where
  open import Agda.Primitive public using (lzero) renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

  Type : (i : ULevel) → Set (lsucc i)
  Type i = Set i

  Type₀ = Type lzero
  Type0 = Type lzero

  Type₁ = Type (lsucc lzero)
  Type1 = Type (lsucc lzero)

  ⟨⟩ : ∀ {i} {A : Type i} {{a : A}} → A
  ⟨⟩ {{a}} = a
