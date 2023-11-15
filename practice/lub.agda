module lub where

open import Data.Nat hiding ( _⊔_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Empty using (⊥; ⊥-elim)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x


ze : ℕ
ze = 0

_⊔_ : ℕ → ℕ → ℕ
zero ⊔ n = n
suc m  ⊔ zero = suc m 
suc n ⊔ suc m = suc (n ⊔ m)

f : (m : ℕ ) → 7 ≡ 7 ⊔ m
f zero = refl 
f m with <-cmp 7 m
... | tri< a ¬b ¬c = {!!} --cant happen , not balnced
... | tri≈ ¬a b ¬c = {!!} --subst (λ k → 7 ≡ k) (refl) (b)
... | tri> ¬a ¬b c = sym (rb c ) where
  rb : suc m ≤ 7 → 7 ⊔ m ≡ 7
  rb (s≤s x) = {!!}
--...| true  = subst (λ k → 7 ≡ 7 ⊔ k) ( {!!} )  ( {!!} )
--...| false = {!!}


x-pro : (n m : ℕ ) → n ≡ m
x-pro n m = {!!}

x : (n m : ℕ)  → n ≡ n ⊔ m
x zero zero = refl
x zero (suc m) = {!!}
x (suc n) zero = refl
x (suc n) (suc m) = cong suc (x n m)


notZeroSuc1 : {n : ℕ} → ¬ (zero ≡ suc n)
notZeroSuc1 ()
notZeroSuc2 : {n : ℕ} → ¬ (suc n ≡ zero) 
notZeroSuc2 ()

l→⊥ : {n : ℕ} → ¬ (suc n ≡ zero) → ⊥
l→⊥ = ?

{-
pro1 : {m n : ℕ} → m ≡ n → ⊥
pro1 = {!!}

pro2 : {m n : ℕ} → ¬ (m ≡ n)
pro2 m n = {!!}
-}

kl : ( l m n : ℕ ) →  m ≡ n → l ≡ m ⊔ n
kl zero zero zero x = refl 
kl zero zero (suc n)  x = ⊥-elim (¬-elim (notZeroSuc1) x) 
kl zero (suc m) zero x = ⊥-elim (¬-elim (notZeroSuc2) x)
kl zero (suc m) (suc n) x = {!!}
kl (suc l) zero zero x = ⊥-elim (l→⊥ ({!!}) (notZeroSuc2)) -- (¬-elim (refl) x)
kl (suc l) zero (suc n) x = {!!} -- if l= n
kl (suc l) (suc m) zero  x = {!!}
kl (suc l) (suc m) (suc n) x = cong suc (kl l m n {!!})

