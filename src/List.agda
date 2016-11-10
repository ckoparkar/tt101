module List where

open import Nat
open import Bool

data List {ℓ} (A : Set ℓ) : Set ℓ where
  [] : List A
  _::_ : (x : A) -> (xs : List A) -> List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _::_  #-}

infixr 6 _::_ _++_

length : ∀ {ℓ} {A : Set ℓ} -> List A -> ℕ
length [] = zero
length (x :: xs) = succ (length xs)

_++_ : ∀ {ℓ} {A : Set ℓ} -> (xs : List A) -> (ys : List A) -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} -> (A -> B) -> (xs : List A) -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : ∀ {ℓ} {A : Set ℓ} -> (A -> 𝔹) -> (xs : List A) -> List A
filter p [] = []
filter p (x :: xs) = let r = filter p xs in
                     if p x then x :: r else r

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  just : A -> Maybe A
  nothing : Maybe A

nth : ∀ {ℓ} {A : Set ℓ} -> ℕ -> List A -> Maybe A
nth zero [] = nothing
nth zero (x :: xs) = just x
nth (succ n) xs = nth n xs

reverse-helper : ∀ {ℓ} {A : Set ℓ} -> List A -> List A -> List A
reverse-helper [] acc = acc
reverse-helper (x :: xs) acc = reverse-helper xs (x :: acc)

reverse : ∀ {ℓ} {A : Set ℓ} -> List A -> List A
reverse xs = reverse-helper xs []

repeat : ∀ {ℓ} {A : Set ℓ} -> ℕ -> (x : A) -> List A
repeat zero x = []
repeat (succ n) x = x :: (repeat n x)

takeWhile : ∀ {ℓ} {A : Set ℓ} -> (p : A -> 𝔹) -> List A -> List A
takeWhile p [] = []
takeWhile p (x :: xs) with p x
takeWhile p (x :: xs) | true = x :: (takeWhile p xs)
takeWhile p (x :: xs) | false = []

take : ∀ {ℓ} {A : Set ℓ} -> (n : ℕ) -> List A -> List A
take zero xs = []
take (succ n) [] = []
take (succ n) (x :: xs) = x :: take n xs

drop : ∀ {ℓ} {A : Set ℓ} -> (n : ℕ) -> List A -> List A
drop zero xs = xs
drop (succ n) [] = []
drop (succ n) (x :: xs) = drop n xs


xs = (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: [])
ys = take 2 xs ++ drop 2 xs
