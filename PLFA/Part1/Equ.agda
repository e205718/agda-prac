module Equ where

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x


sym : ∀ {A : Set} {x y : A} --symmetric 
 → x ≡ y
 → y ≡ x
sym refl = refl


