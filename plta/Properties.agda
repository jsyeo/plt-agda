module plta.Properties where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

  +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc zero n p = refl
  +-assoc (suc m) n p =
    begin
      (suc m + n) + p
    ≡⟨⟩
      suc (m + n) + p
    ≡⟨⟩
      suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
      suc (m + (n + p))
    ≡⟨⟩
      suc m + (n + p)
    ∎

  +-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
  +-identityʳ zero = refl
  +-identityʳ (suc m) =
    begin
      suc m + zero
    ≡⟨⟩
      suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
      suc m
    ∎

  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n = refl
  +-suc (suc m) n =
    begin
      suc m + suc n
    ≡⟨⟩
      suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
      suc (suc (m + n))
    ≡⟨⟩
      suc (suc m + n)
    ∎
  
  +-commutativity : ∀ (m n : ℕ) → m + n ≡ n + m
  +-commutativity m zero = +-identityʳ m
  +-commutativity m (suc n) =
    begin
      m + suc n
    ≡⟨ +-suc m n ⟩
      suc (m + n)
    ≡⟨ cong suc (+-commutativity m n) ⟩
      suc (n + m)
    ≡⟨⟩
      suc n + m
    ∎

  +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc′ zero n p = refl
  +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

  +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
  +-swap zero n p = refl
  +-swap (suc m) n p rewrite +-commutativity n p | sym (+-assoc m p n) | +-commutativity (suc (m + p)) n = refl
{-
  +-swap (suc m) n p =
    begin
      suc m + (n + p)
    ≡⟨⟩
      suc (m + (n + p))
    ≡⟨ +-commutativity n p ⟩
      suc (m + (p + n))
    ≡⟨ sym (+-assoc m p n) ⟩
      suc ((m + p) + n)
    ≡⟨⟩
      suc (m + p) + n
    ≡⟨ +-commutativity (suc (m + p)) n ⟩
      n + (suc m + p)
    ∎
-}
