module PracRelation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _≤_ : ℕ → ℕ → Set where
 z≤n : ∀ {n : ℕ}
  → zero ≤ n
 s≤s : ∀ {m n : ℕ}
  → m ≤ n
  → suc m ≤ suc n

prac1 : 4 ≤ 6
prac1 = s≤s (s≤s (s≤s (s≤s z≤n)))

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

inv-s≤s : { m n : ℕ }
 → suc m ≤ suc n
 → m ≤ n
inv-s≤s (s≤s l ) = l

inv-z≤n : {n : ℕ} → n ≤ zero → n ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
 → m ≤ n
 → n ≤ p
 → m ≤ p
≤-trans z≤n b = z≤n
≤-trans (s≤s a) (s≤s b) = s≤s (≤-trans a b)


≤-antisym : ∀ {m n : ℕ}
 → m ≤ n
 → n ≤ m
 → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s a) (s≤s b) = cong suc (≤-antisym a b)

data Total (m n : ℕ) : Set where
  forward :
    m ≤ n
     → Total m n
  flipped :
    n ≤ m
     → Total m n
  zeroed : 
    m ≡ n
     → Total m n
     
≤-total : ∀ (m n  : ℕ) → Total m n
≤-total zero zero = zeroed refl
≤-total zero n = forward z≤n 
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward x = forward (s≤s x)
... | flipped x = flipped (s≤s x)
... | zeroed t  = zeroed (cong suc t)

