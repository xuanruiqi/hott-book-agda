{-# OPTIONS --without-K --exact-split --safe #-}

module Natural where
  open import Data.Nat
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; subst; sym; cong; [_])
  open Eq.≡-Reasoning
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Unit using (⊤; tt)

  code : ℕ → ℕ → Set
  code 0 0 = ⊤
  code (suc m) 0 = ⊥
  code 0 (suc n) = ⊥
  code (suc m) (suc n) = code m n

  r : ∀ (n : ℕ) → code n n
  r 0 = tt
  r (suc n) = r n
  
  encode : ∀ (m n : ℕ) → (m ≡ n) → code m n
  encode m _ eq-m-n rewrite (sym eq-m-n) = r m

  decode : ∀ (m n : ℕ) → code m n → m ≡ n
  decode zero zero coded = refl
  decode (suc m) (suc n) coded = cong suc (decode m n coded)
  
  decode-r : ∀ (n : ℕ) → decode n n (r n) ≡ refl
  decode-r zero = refl
  decode-r (suc n) rewrite (decode-r n) = refl

  decode-encode : ∀ (m n : ℕ) → (p : m ≡ n) → decode m n (encode m n p) ≡ p
  decode-encode m m refl rewrite (decode-r m) = refl

  encode-suc : ∀ (m n : ℕ) → (p : m ≡ n) → encode (suc m) (suc n) (cong suc p) ≡ encode m n p
  encode-suc m n refl = refl

  encode-decode : ∀ (m n : ℕ) → (c : code m n) → encode m n (decode m n c) ≡ c
  encode-decode zero zero tt = refl
  encode-decode (suc m) (suc n) c rewrite encode-suc m n (decode m n c)
                                        | encode-decode m n c           = refl
