module lub where

open import Data.Nat hiding ( _⊔_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Empty --using (⊥; ⊥-elim)
open import Data.Nat.Properties
open import Relation.Nullary.Negation


--¬_ : Set → Set
--¬ A = A → ⊥

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
l→⊥ = {!!}

{-
pro1 : {m n : ℕ} → m ≡ n → ⊥
pro1 = {!!}

pro2 : {m n : ℕ} → ¬ (m ≡ n)
pro2 m n = {!!}
-}
sm : {m n : ℕ} → suc m ≡ suc n → m ≡ n
sm refl = refl


pro1 : { m : ℕ } → zero ≡ suc m → ⊥
pro1 ()

pro2 : {m : ℕ } → suc m ≡ zero → ⊥ 
pro2 ()

notSucZero : ∀ {n} → ¬ suc n ≡ 0
notSucZero contra with 1+n≢0 contra
... | ()

sucNotZero : ∀ {n : ℕ } → suc n ≢ zero
sucNotZero = λ ()


kl : ( l m n : ℕ ) →  m ≡ n → l ≡ m ⊔ n
kl zero zero zero x = refl 
kl zero zero (suc n)  x = ⊥-elim (notZeroSuc1 x) 
kl zero (suc m) zero x = ⊥-elim (notZeroSuc2 x)
kl zero (suc m) (suc n) x = ⊥-elim (pro2 ( sym (kl zero (suc m) (suc n) x)))
kl (suc l) zero zero x = ⊥-elim (pro2 (kl (suc l) zero zero x))
kl (suc l) zero (suc n) x with <-cmp (suc l) (suc n)
... | tri< a ¬b ¬c = ⊥-elim (¬b (kl (suc l) zero (suc n) x))
... | tri≈ ¬a b ¬c = cong suc (sm b)
... | tri> ¬a ¬b c = ⊥-elim (¬b (kl (suc l) zero (suc n) x))
kl (suc l) (suc m) zero  x with <-cmp (suc l) (suc m)
... | tri< a ¬b ¬c = ⊥-elim (¬b (kl (suc l) (suc m) zero x))
... | tri≈ ¬a b ¬c = cong suc (sm b)
... | tri> ¬a ¬b c = ⊥-elim (¬b (kl (suc l) (suc m) zero x))
kl (suc l) (suc m) (suc n) x = cong suc (kl l m n (sm x)) -- suc (kl l m n x)

ks :(l m n : ℕ) → m ≡ n → l ≡ m ⊔ n
ks l m n x with <-cmp m n
ks zero zero zero x | tri< a ¬b ¬c = refl
ks zero zero (suc n) x | tri< a ¬b ¬c = {!!}
ks zero (suc m) n x | tri< a ¬b ¬c = {!!}
ks (suc l) m n x | tri< a ¬b ¬c = {!!}
... | tri≈ ¬a b ¬c = {!!}
... | tri> ¬a ¬b c = {!!}
