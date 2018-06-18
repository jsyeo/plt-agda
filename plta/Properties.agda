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

  *-identity : ∀ (m : ℕ) → m * 0 ≡ 0
  *-identity zero = refl
  *-identity (suc m) rewrite *-identity m = refl

  *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ zero n p = refl
  *-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl

  *-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
  *-suc zero n = refl
  *-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl
  
  *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
  *-comm m zero rewrite *-identity m = refl
  *-comm m (suc n) rewrite *-suc m n | *-comm m n = refl

  ∸-zero-monus-n : ∀ (n : ℕ) → 0 ∸ n ≡ 0
  ∸-zero-monus-n zero = refl
  ∸-zero-monus-n (suc n) = refl

  ∸-+-assoc : ∀ (m n p : ℕ ) → m ∸ n ∸ p ≡ m ∸ (n + p)
  ∸-+-assoc zero n p rewrite ∸-zero-monus-n n | ∸-zero-monus-n p | ∸-zero-monus-n (n + p) = refl
  ∸-+-assoc (suc m) zero p = refl
  ∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl
  
