module plta.Relations where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (+-comm; +-suc)

  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {m : ℕ} → zero ≤ m
    s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n


  _ : 2 ≤ 4
  _ = s≤s (s≤s z≤n)


  ≤-refl : ∀ {n : ℕ} → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s (≤-refl {n})


