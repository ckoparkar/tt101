module Bool where

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

-- {-# BUILTIN BOOL 𝔹 #-}
-- {-# BUILTIN TRUE true #-}
-- {-# BUILTIN FALSE false #-}

¬_ : 𝔹 -> 𝔹
¬_ true = false
¬_ false = true

_&&_ : 𝔹 -> 𝔹 -> 𝔹
true && y = y
false && y = false

_||_ : 𝔹 -> 𝔹 -> 𝔹
true || y = true
false || y = y

_xor_ : 𝔹 -> 𝔹 -> 𝔹
_xor_ true true = false
_xor_ false false = false
_xor_ _ _ = true

_imp_ : 𝔹 -> 𝔹 -> 𝔹
true imp b2 = b2
false imp b2 = true

_nand_ : 𝔹 -> 𝔹 -> 𝔹
_nand_ b1 b2 = ¬ (b1 && b2)

_nor_ : 𝔹 -> 𝔹 -> 𝔹
_nor_ b1 b2 = ¬ (b1 || b2)

if_then_else_ : ∀ {ℓ} {A : Set ℓ} -> 𝔹 -> A -> A -> A
if true then y else z = y
if false then y else z = z

infix 7 ¬_
infixr 6 _&&_
infixr 5 _||_
infixl 6 _xor_
infixl 6 _imp_
