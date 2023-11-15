module Iso where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {a b c : Set} → (b → c) → (a → b) → (a → c)
(g ∘ f) x = g (f x)

_∘′_ : ∀ {a b c : Set} → (b → c) → (a → b) → (a → c)
(g ∘′ f) = λ x → g (f x)

postulate
 extensionality : ∀ {a b  : Set} {f g : a → b}
   → (∀ (x : a) → f x ≡ g x )
   → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
 where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m  → extensionality (λ n → same-app m n) )

postulate
 ∀-extensionality : {A : Set}  {B : A →  Set} {f g : ∀ (x : A) → B x }
  → (∀ (x : A) → f x ≡ g x)
  → f ≡ g
  
record _≃_  (A B : Set) : Set where
 field
  to : A → B
  from : B → A
  from∘to : ∀ (x : A) → from (to x) ≡ x
  to∘from : ∀ (y : B) → to (from y ) ≡ y
 
