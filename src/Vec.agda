module Vec where

open import Nat
open import Bool
open import BoolProofs
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; inspect)

data 𝕍 {ℓ} (A : Set ℓ) : ℕ -> Set ℓ where
  [] : 𝕍 A 0
  _::_ : {n : ℕ} (x : A) (xs : 𝕍 A n) -> 𝕍 A (succ n)

_++𝕍_ : ∀ {ℓ} {A : Set ℓ} {n m : ℕ} -> (xs : 𝕍 A m) -> (ys : 𝕍 A n) -> 𝕍 A (m + n)
[] ++𝕍 ys = ys
(x :: xs) ++𝕍 ys = x :: (xs ++𝕍 ys)

head𝕍 : ∀ {ℓ} {A : Set ℓ} {n : ℕ} -> (xs : 𝕍 A (succ n)) -> A
head𝕍 (x :: xs) = x

tail𝕍 : ∀ {ℓ} {A : Set ℓ} {n : ℕ} -> (xs : 𝕍 A (succ n)) -> 𝕍 A n
tail𝕍 (x :: xs) = xs

map𝕍 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : ℕ} -> (A -> B) -> 𝕍 A n -> 𝕍 B n
map𝕍 f [] = []
map𝕍 f (x :: xs) = f x :: map𝕍 f xs

nth𝕍 : ∀ {ℓ} {A : Set ℓ} {m : ℕ} -> (n : ℕ) -> n < m ≡ true -> 𝕍 A m -> A
nth𝕍 zero p [] = 𝔹-contra p
nth𝕍 (succ n) p [] = 𝔹-contra p
nth𝕍 zero p (x :: xs) = x
nth𝕍 (succ n) p (x :: xs) = nth𝕍 n p xs

repeat𝕍 : ∀ {ℓ} {A : Set ℓ} -> (a : A) -> (n : ℕ) -> 𝕍 A n
repeat𝕍 a zero = []
repeat𝕍 a (succ n) = a :: repeat𝕍 a n
