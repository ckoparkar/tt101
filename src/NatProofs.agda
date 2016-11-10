module NatProofs where

open import Nat
open import Bool
open import BoolProofs
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

+0 : ∀ (m : ℕ) -> 0 + m ≡ m
+0 p = refl

+0a : ∀ (m : ℕ) -> m + 0 ≡ m
+0a zero = refl
+0a (succ m) rewrite +0a m = refl

+-assoc : ∀ (m n o : ℕ) -> m + (n + o) ≡ (m + n) + o
+-assoc zero n o = refl
+-assoc (succ m) n o rewrite +-assoc m n o = refl

+-succ : ∀ (m n : ℕ) -> m + succ n ≡ succ (m + n)
+-succ zero n = refl
+-succ (succ m) n rewrite +-succ m n = refl

succ1 : ∀ (m : ℕ) -> succ m ≡ m + 1
succ1 zero = refl
succ1 (succ m) rewrite succ1 m = refl

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m zero = +0a m
+-comm m (succ n) rewrite +-comm n m = +-succ m n

*-distr : ∀ (m n o : ℕ) -> (m + n) * o ≡ m * o + n * o
*-distr zero n o = refl
*-distr (succ m) n o rewrite *-distr m n o = +-assoc o (m * o) (n * o)

*-distl : ∀ (m n o : ℕ) -> m * (n + o) ≡ m * n + m * o
*-distl zero n o = refl
*-distl (succ m) n o rewrite *-distl m n o
  | +-assoc (n + o) (m * n) (m * o)
  | +-assoc (n + m * n) o (m * o)
  | +-comm (n + o) (m * n)
  | +-assoc (m * n) n o
  | +-comm n (m * n) = refl 

*0 : ∀ (m : ℕ) -> m * zero ≡ zero
*0 zero = refl
*0 (succ m) rewrite *0 m = refl

*1 : ∀ (m : ℕ) -> m * 1 ≡ m
*1 zero = refl
*1 (succ m) rewrite *1 m = refl

*-succ : ∀ (m n : ℕ) -> m * (succ n) ≡ m + m * n
*-succ zero n = refl
*-succ (succ m) n rewrite *-succ m n | +-assoc m n (m * n) | +-assoc n m (m * n) | +-comm m n = refl

*-comm : ∀ (m n : ℕ) -> m * n ≡ n * m
*-comm zero n = sym (*0 n)
*-comm (succ m) n rewrite *-comm m n = sym (*-succ n m)

<-0 : ∀ (m : ℕ) → m < 0 ≡ false
<-0 zero = refl
<-0 (succ m) = refl

<-trans : ∀ {m n o : ℕ} -> m < n ≡ true -> n < o ≡ true -> m < o ≡ true
<-trans {zero} {zero} {zero} p1 p2 = 𝔹-contra p1
<-trans {zero} {zero} {(succ o)} p1 p2 = refl
<-trans {zero} {(succ n)} {zero} p1 p2 = 𝔹-contra p2
<-trans {zero} {(succ n)} {(succ o)} p1 p2 = refl
<-trans {succ m} {zero} {zero} p1 p2 = 𝔹-contra p1
<-trans {succ m} {zero} {succ o} p1 p2 rewrite <-0 m = 𝔹-contra p1
<-trans {succ m} {succ n} {zero} p1 p2 = 𝔹-contra p2
<-trans {succ m} {succ n} {succ o} p1 p2 = <-trans {m} {n} {o} p1 p2

0-≤ : ∀ (m : ℕ) -> 0 ≤ m ≡ true
0-≤ zero = refl
0-≤ (succ m) = refl

≤-trans : ∀ {m n o : ℕ} -> m ≤ n ≡ true -> n ≤ o ≡ true -> m ≤ o ≡ true
≤-trans {zero} {zero} {zero} p1 p2 = refl
≤-trans {zero} {zero} {(succ o)} p1 p2 = refl
≤-trans {zero} {(succ n)} {zero} p1 p2 = refl
≤-trans {zero} {(succ n)} {succ o} p1 p2 = refl
≤-trans {succ m} {zero} {o} p1 p2 = 𝔹-contra p1
≤-trans {succ m} {succ n} {zero} p1 p2 = 𝔹-contra p2
≤-trans {succ m} {succ n} {succ o} p1 p2 rewrite ≤-trans {m} {n} {o} p1 p2 = refl

≤-succ : ∀ (m : ℕ) -> m ≤ (succ m) ≡ true
≤-succ zero = refl
≤-succ (succ m) rewrite ≤-succ m = refl

=ℕ-refl : ∀ (n : ℕ) -> n =ℕ n ≡ true
=ℕ-refl zero = refl
=ℕ-refl (succ n) rewrite =ℕ-refl n = refl

=ℕ-to-≣ : ∀ {m n : ℕ} -> m =ℕ n ≡ true -> m ≡ n
=ℕ-to-≣ {zero} {zero} p = refl
=ℕ-to-≣ {succ m} {zero} p = 𝔹-contra p
=ℕ-to-≣ {zero} {succ n} p = 𝔹-contra p
=ℕ-to-≣ {succ m} {succ n} p rewrite =ℕ-to-≣ {m} {n} p = refl

=ℕ-from≡ : ∀ {m n : ℕ} -> m ≡ n -> m =ℕ n ≡ true
=ℕ-from≡ {m} refl = =ℕ-refl m

=ℕ-sym : ∀ (m n : ℕ) -> (m =ℕ n) ≡ (n =ℕ m)
=ℕ-sym zero zero = refl
=ℕ-sym zero (succ n) = refl
=ℕ-sym (succ m) zero = refl
=ℕ-sym (succ m) (succ n) rewrite =ℕ-sym m n = refl

=ℕ-succ : ∀ (m : ℕ) -> m =ℕ succ m ≡ false
=ℕ-succ zero = refl
=ℕ-succ (succ m) rewrite =ℕ-succ m = refl
