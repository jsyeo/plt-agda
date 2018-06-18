import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

module plta.Naturals where
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ


  {-# BUILTIN NATURAL ℕ #-}
  
  _+_ : ℕ → ℕ → ℕ
  0       + n = n
  (suc m) + n = suc (m + n)

  _ : 2 + 3 ≡ 5
  _ =
    begin
      2 + 3
    ≡⟨⟩
      suc (1 + 3)
    ≡⟨⟩
      suc (suc (0 + 3))
    ≡⟨⟩
      suc (suc 3)
    ≡⟨⟩
      5
    ∎

  proof₁ : 2 + 3 ≡ 5
  proof₁ = refl

  _ : 3 + 4 ≡ 7
  _ =
    begin
      3 + 4
    ≡⟨⟩
      suc (2 + 4)
    ≡⟨⟩
      suc (suc (1 + 4))
    ≡⟨⟩
      suc (suc (suc (0 + 4)))
    ≡⟨⟩
      suc (suc (suc 4))
    ≡⟨⟩
      7
    ∎

  _*_ : ℕ → ℕ → ℕ
  0 * n       = 0
  (suc m) * n = n + (m * n)

  _^_ : ℕ → ℕ → ℕ
  n ^ 0       = 1
  n ^ (suc m) = n * (n ^ m)
  
  _∸_ : ℕ → ℕ → ℕ
  m       ∸ zero     =  m
  zero    ∸ (suc n)  =  zero
  (suc m) ∸ (suc n)  =  m ∸ n

  _p_ : ℕ → ℕ → ℕ
  zero p n = n
  suc m p n = suc (m p n)
