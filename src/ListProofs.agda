module ListProofs where

open import Nat
open import NatProofs
open import Bool
open import BoolProofs
open import List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; inspect)

length-++ : ∀ {ℓ} {A : Set ℓ} (l1 l2 : List A) -> length (l1 ++ l2) ≡ length l1 + length l2
length-++ [] l2 = refl
length-++ (x :: l1) l2 rewrite length-++ l1 l2 = refl

++-assoc : ∀ {ℓ} {A : Set ℓ} (l1 l2 l3 : List A) -> (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x :: l1) l2 l3 rewrite ++-assoc l1 l2 l3 = refl

length-filter : ∀ {ℓ} {A : Set ℓ} (p : (A -> 𝔹)) (l : List A) ->
                length (filter p l) ≤ length l ≡ true
length-filter p [] = refl
length-filter p (x :: l) with p x
length-filter p (x :: l) | true rewrite length-filter p l = refl
length-filter p (x :: l) | false = ≤-trans {(length (filter p l))}
                                           (length-filter p l)
                                           (≤-succ (length l))


-- filter-idem : ∀ {ℓ} {A : Set ℓ} (p : (A -> 𝔹)) (l : List A) ->
--               filter p l ≡ filter p (filter p l)


length-reverse-helper : ∀ {ℓ} {A : Set ℓ}  (h l : List A) -> length (reverse-helper h l) ≡
                                                             length h + length l
length-reverse-helper [] l = refl
length-reverse-helper (x :: h) l rewrite length-reverse-helper h (x :: l) = +-succ (length h) (length l)

reverse-length : ∀ {ℓ} {A : Set ℓ} -> (l : List A) -> length l ≡ length (reverse l)
reverse-length [] = refl
reverse-length (x :: l) rewrite length-reverse-helper l (x :: []) = succ1 (length l)

-- twr : ∀ {ℓ} {A : Set ℓ} {a : A} (p : A -> 𝔹) -> (n : ℕ) -> p a ≡ true -> takeWhile p (repeat n a) ≡ repeat n a
-- twr p zero p1 = refl
-- twr p (succ n) p1 = {!!}

take-drop : ∀ {ℓ} {A : Set ℓ} (n : ℕ) -> (xs : List A) -> take n xs ++ drop n xs ≡ xs
take-drop zero xs = refl
take-drop (succ n) [] = refl
take-drop (succ n) (x :: xs) rewrite take-drop n xs = refl
