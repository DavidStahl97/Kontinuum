module Kontinuum.FareySequence where

    open import Relation.Nullary.Decidable
    open import Relation.Binary.PropositionalEquality
    open import Data.List
    open import Data.Nat as ℕ using (ℕ)
    open import Data.Nat.Properties
    open import Data.Integer as ℤ using (ℤ)

    open ≤-Reasoning

    record F : Set where
        constructor _/_
        field
            n : ℤ
            d : ℕ
    
    AddBetween : ℕ → List F → List F 
    AddBetween i [] = []
    AddBetween i (x ∷ []) = x ∷ []
    AddBetween i (x ∷ y ∷ tail) with AddBetween i (y ∷ tail) | F.d x ℕ.+ F.d y ℕ.≥? i
    ... | rec | yes _ = x ∷ ((F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y)) ∷ rec
    ... | rec | no _ = x ∷ rec

    Fₙ : ℤ → ℕ → List F
    Fₙ start 0 = (start / 1) ∷ (ℤ.suc start / 1) ∷ []     
    Fₙ start (ℕ.suc iter) = AddBetween (ℕ.suc iter) (Fₙ start iter)

    AddBetween≥Fₙ : ∀ (n : ℕ) (l : List F) → length (AddBetween n l) ℕ.≥ length l
    AddBetween≥Fₙ n [] = ℕ.z≤n
    AddBetween≥Fₙ n (x ∷ []) = ℕ.s≤s (ℕ.z≤n)
    AddBetween≥Fₙ n (x ∷ y ∷ tail) with AddBetween≥Fₙ n (y ∷ tail) | F.d x ℕ.+ F.d y ℕ.≥? n
    ... | rec | yes _ = begin 
        length (x ∷ y ∷ tail) ≤⟨ ℕ.s≤s (ℕ.s≤s (m≤n⇒m≤1+n (≤-reflexive refl))) ⟩ 
        length (x ∷ ((F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y)) ∷ y ∷ tail) ≤⟨ ℕ.s≤s (ℕ.s≤s rec) ⟩ 
        length (x ∷ ((F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y)) ∷ AddBetween n (y ∷ tail)) ∎
    ... | rec | no _ = begin 
        length (x ∷ y ∷ tail) ≤⟨ ℕ.s≤s rec ⟩ 
        length (x ∷ AddBetween n (y ∷ tail)) ∎

    Fₙ+1≥Fₙ : ∀ (z : ℤ) (n : ℕ) → length (Fₙ z (1 ℕ.+ n)) ℕ.≥ length (Fₙ z n)
    Fₙ+1≥Fₙ z ℕ.zero = ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))
    Fₙ+1≥Fₙ z (ℕ.suc n) = AddBetween≥Fₙ (2 ℕ.+ n) (AddBetween (1 ℕ.+ n) (Fₙ z n))

    length≥2 : ∀ (z : ℤ) (n : ℕ) → length (Fₙ z n) ℕ.≥ 2
    length≥2 z ℕ.zero = ≤-reflexive refl
    length≥2 z (ℕ.suc n) = begin 
        2 ≤⟨ length≥2 z n ⟩ 
        length (Fₙ z n) ≤⟨ Fₙ+1≥Fₙ z n ⟩
        length (Fₙ z (ℕ.suc n)) ∎
 