module Nat where

open import Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ -> ℕ -> ℕ
zero + n = n
succ m + n = succ (m + n)

_*_ : ℕ -> ℕ -> ℕ
zero * n = zero
succ m * n = n + (m * n)

infixl 7 _*_
infixl 6 _+_

_<_ : ℕ -> ℕ -> 𝔹
zero < zero = false
zero < (succ n) = true
(succ n) < zero = false
succ m < succ n = m < n

_=ℕ_ : ℕ -> ℕ -> 𝔹
zero =ℕ zero = true
succ m =ℕ succ n = m =ℕ n
_ =ℕ _ = false

_≤_ : ℕ -> ℕ -> 𝔹
_≤_ m n = (m < n) || (m =ℕ n)

_>_ : ℕ -> ℕ -> 𝔹
zero > zero = false
zero > succ n = false
succ m > zero = true
succ m > succ n = m > n

_≥_ : ℕ -> ℕ -> 𝔹
_≥_ m n = (m > n) || (m =ℕ n)

infixl 5 _<_ _=ℕ_ _≤_ _>_

iszero : (n : ℕ) -> 𝔹
iszero zero = true
iszero (succ n) = false

iseven : (n : ℕ) -> 𝔹
iseven zero = true
iseven 1 = false
iseven (succ (succ n)) = iseven n
