module BoolProofs where

open import Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

¬¬-same : ∀ {b} -> ¬ ¬ b ≡ b
¬¬-same {true} = refl
¬¬-same {false} = refl

&&-same : ∀ {b} -> b && b ≡ b
&&-same {true} = refl
&&-same {false} = refl

||-ff₁ : ∀ {b1 b2} -> ((b1 || b2) ≡ false) -> b1 ≡ false
||-ff₁ {false} p = refl
||-ff₁ {true} ()

||-cong₁ : ∀ {b1 b1' b2} -> (b1 ≡ b1') -> (b1 || b2) ≡ (b1' || b2)
||-cong₁ refl = refl

||-cong₂ : ∀ {b1 b2 b2'} -> (b2 ≡ b2') -> (b1 || b2) ≡ (b1 || b2')
||-cong₂ p rewrite p = refl

ite-same : ∀ {l} {A : Set l} -> ∀ (b : 𝔹) (x : A) -> (if b then x else x) ≡ x
ite-same true x = refl
ite-same false x = refl

&&-fst : ∀ {b1 b2} -> b1 && b2 ≡ true -> b1 ≡ true
&&-fst {true} p = refl
&&-fst {false} ()

&&-snd : ∀ {b1 b2} -> b1 && b2 ≡ true -> b2 ≡ true
&&-snd {true} refl = refl
&&-snd {false} ()

&&-combo : ∀ {b1 b2} -> b1 ≡ true -> b2 ≡ true -> b1 && b2 ≡ true
&&-combo refl refl = refl

&&-false : ∀ (b : 𝔹) -> b && false ≡ false
&&-false true = refl
&&-false false = refl

imp-ff : ∀ (b : 𝔹) -> false imp b ≡ true
imp-ff true = refl
imp-ff false = refl

&&-contra : ∀ (b : 𝔹) -> false && b ≡ false
&&-contra true = refl
&&-contra false = refl

&&-comm : ∀ (b1 b2 : 𝔹) -> b1 && b2 ≡ b2 && b1
&&-comm true true = refl
&&-comm true false = refl
&&-comm false true = refl
&&-comm false false = refl

𝔹-contra : false ≡ true → ∀{ℓ} {P : Set ℓ} → P
𝔹-contra ()
