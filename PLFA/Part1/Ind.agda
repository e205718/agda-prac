module Ind where

import Relation.Binary.PropositionalEquality as Eq
open Eq 
open Eq.≡-Reasoning --using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
   ≡⟨⟩
    7 + 5
   ≡⟨⟩
    12
   ≡⟨⟩
    3 + 9
   ≡⟨⟩
    3 + (4 + 5)
   ∎

-- Our first proof : associativity. 
-- ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
 begin
  ( zero + n ) + p
 ≡⟨⟩
  n + p
 ≡⟨⟩
  zero + (n + p)
 ≡⟨⟩
  n + p
 ∎
+-assoc (suc m) n p = 
 begin
  (suc m + n) + p
 ≡⟨⟩
  suc (m + n) + p
 ≡⟨⟩
  suc ((m + n) + p)
 ≡⟨ cong suc (+-assoc m n p) ⟩
  suc ( m + (n + p) )
 ≡⟨⟩
  suc m + (n + p)
 ∎

--Our second proof : commutativity
-- m + n ≡ n + m

lemma1 : ∀(n : ℕ) → zero + n ≡ n
lemma1 n =
 begin
  zero + n
 ≡⟨⟩
  n
 ∎

+-identity : (m : ℕ) → m + zero ≡ m
+-identity zero = refl
+-identity (suc m) =
 begin
  suc m + zero
 ≡⟨⟩
  suc (m + zero)
 ≡⟨ cong suc (+-identity m) ⟩
  suc (zero + m)
 ≡⟨⟩
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

lemma6 : (n : ℕ) → suc n ≡ n + 1
lemma6 zero = refl
lemma6 (suc n) =
 begin
  suc (suc n)
 ≡⟨ cong suc (lemma6 n ) ⟩
  suc n + 1
 ∎

lemma8 : (n : ℕ) → n + zero ≡ zero + n
lemma8 zero = refl
lemma8 (suc n) = cong suc (+-identity n)

lemma5 : (n : ℕ) → 1 + n ≡ n + 1
lemma5 zero = lemma8 1
lemma5 (suc n) =
 begin
  1 + suc n
 ≡⟨ cong suc refl ⟩
  suc (1 + n)
 ≡⟨ cong suc (lemma6 n) ⟩
  suc (n + 1)
 ≡⟨⟩
  suc n + 1
 ∎

lemma7 : ( m n : ℕ) → n + m ≡ m + n 
lemma7 zero n = lemma8 n
lemma7 (suc m) n =
 begin
  n + suc m
 ≡⟨ +-suc n m  ⟩
  suc (n + m)
 ≡⟨ cong (suc) (lemma7 m n) ⟩
  suc (m + n)
 ≡⟨⟩
  suc m + n
 ∎


lemma4 : ∀ ( m n : ℕ) → suc (n + m) ≡ n + suc m 
lemma4 zero n =
 begin
  suc (n + zero)
 ≡⟨ cong (suc) (+-identity n) ⟩
  suc (zero + n)
 ≡⟨⟩
  suc zero + n
 ≡⟨ lemma5 n ⟩
  n + suc zero
 ∎
lemma4 (suc m) n =
 begin
   suc (n + suc m)
  ≡⟨ cong suc (sym (lemma4 m n )) ⟩
   suc ( suc n + m)
  ≡⟨⟩
   suc (suc (n + m) )
  ≡⟨ cong suc (cong suc (lemma7 m n)) ⟩
   suc (suc (m + n))
  ≡⟨⟩
   suc (suc m + n)
  ≡⟨⟩
   (suc (suc m)) + n 
  ≡⟨ lemma7 n (suc (suc m)) ⟩
   n + (suc (suc m))
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero zero = refl
+-comm zero (suc n) = cong (suc) (+-comm zero n)
+-comm (suc m) n =
 begin
  suc m + n
 ≡⟨⟩
  suc (m + n)
 ≡⟨ cong (suc) (+-comm m n) ⟩
  suc (n + m)
 ≡⟨ lemma4 m n ⟩
  n + suc m
 ∎
 

lemma2 : ( m n : ℕ) → suc m + n ≡ suc (n + m)
lemma2 zero n =
 begin
  suc zero + n
 ≡⟨⟩
  suc (zero + n)
 ≡⟨ cong suc (sym (+-identity n ) ) ⟩
  suc (n + zero)
 ∎
  
lemma2 (suc m) n =
 begin
  suc (suc m ) + n
 ≡⟨⟩
  suc (suc m + n) -- suc (n + suc m)
 ≡⟨⟩
  suc (suc (m + n))
 ≡⟨ cong suc ( cong suc (+-comm m n)) ⟩
  suc (suc (n + m))
 ≡⟨ cong suc (lemma4 m n ) ⟩
  suc ( n + suc m)
 ∎
