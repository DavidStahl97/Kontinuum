module Kontinuum.FareySequence where

    open import Relation.Nullary.Decidable
    open import Relation.Binary.PropositionalEquality
    open import Data.List.Membership.Propositional renaming (_∈_ to _∈ₚ_)
    open import Data.Maybe
    open import Data.Fin
    open import Data.List
    open import Data.List.Relation.Unary.All
    open import Data.Product
    open import Data.Nat as ℕ using (ℕ)
    open import Data.Nat.Properties
    open import Data.Integer as ℤ using (ℤ)
    import Data.Integer.Properties as ℤProp

    record F : Set where
        constructor _/_
        field
            n : ℤ
            d : ℕ
    
    private
        InBetween : F → F → F
        InBetween x y = (F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y)

        concateF : ℕ → F → (l : List F) → length l ℕ.≥ 1 → Σ (List F) λ l → length l ℕ.≥ 2
        concateF i x (y ∷ tail) tail≥1 with F.d x ℕ.+ F.d y ℕ.≥? i
        ... | yes _ = x ∷ InBetween x y ∷ y ∷ tail , ℕ.s≤s (ℕ.s≤s ℕ.z≤n)
        ... | no _ = x ∷ y ∷ tail , ℕ.s≤s (ℕ.s≤s ℕ.z≤n)

        AddBetween : ℕ → (l : List F) → length l ℕ.≥ 2 → Σ (List F) λ l → length l ℕ.≥ 2
        AddBetween i (x ∷ []) (ℕ.s≤s ())
        AddBetween i (x ∷ y ∷ []) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) = concateF i x (y ∷ []) ?
        AddBetween i (x ∷ y ∷ x₁ ∷ l) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) = concateF i x (AddBetween i (y ∷ x₁ ∷ l) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) ?  

{--
        ΣFₙ×→≥2 : ℤ → ℕ → Σ (List F) λ l → length l ℕ.≥ 2
        ΣFₙ×→≥2 z ℕ.zero = (z / 1) ∷ (ℤ.suc z / 1) ∷ [] , (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
        ΣFₙ×→≥2 z (ℕ.suc n) with ΣFₙ×→≥2 z n
        ... | l , l≥2 = AddBetween (ℕ.suc n) l l≥2 , {! (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))  !}

    Fₙ : ℤ → ℕ → List F
    Fₙ start 0 = (start / 1) ∷ (ℤ.suc start / 1) ∷ []     
    Fₙ start (ℕ.suc iter) = AddBetween (ℕ.suc iter) (Fₙ start iter)


    ---- 
    -- Properties --
    ----

    private
        AddBetween≥Fₙ : ∀ (n : ℕ) (l : List F) → length (AddBetween n l) ℕ.≥ length l
        AddBetween≥Fₙ n [] = ℕ.z≤n
        AddBetween≥Fₙ n (x ∷ []) = ℕ.s≤s (ℕ.z≤n)
        AddBetween≥Fₙ n (x ∷ y ∷ tail) with AddBetween≥Fₙ n (y ∷ tail) | F.d x ℕ.+ F.d y ℕ.≥? n
        ... | rec | yes _ = begin 
            length (x ∷ y ∷ tail) ≤⟨ ℕ.s≤s (ℕ.s≤s (m≤n⇒m≤1+n (≤-reflexive refl))) ⟩ 
            length (x ∷ ((F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y)) ∷ y ∷ tail) ≤⟨ ℕ.s≤s (ℕ.s≤s rec) ⟩ 
            length (x ∷ ((F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y)) ∷ AddBetween n (y ∷ tail)) ∎
            where open ≤-Reasoning
        ... | rec | no _ = begin 
            length (x ∷ y ∷ tail) ≤⟨ ℕ.s≤s rec ⟩ 
            length (x ∷ AddBetween n (y ∷ tail)) ∎
            where open ≤-Reasoning

    Fₙ+1≥Fₙ : ∀ (z : ℤ) (n : ℕ) → length (Fₙ z (1 ℕ.+ n)) ℕ.≥ length (Fₙ z n)
    Fₙ+1≥Fₙ z ℕ.zero = ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))
    Fₙ+1≥Fₙ z (ℕ.suc n) = AddBetween≥Fₙ (2 ℕ.+ n) (AddBetween (1 ℕ.+ n) (Fₙ z n))

    Fₙlength≥2 : ∀ (z : ℤ) (n : ℕ) → length (Fₙ z n) ℕ.≥ 2
    Fₙlength≥2 z ℕ.zero = ≤-reflexive refl
    Fₙlength≥2 z (ℕ.suc n) = begin 
        2 ≤⟨ Fₙlength≥2 z n ⟩ 
        length (Fₙ z n) ≤⟨ Fₙ+1≥Fₙ z n ⟩
        length (Fₙ z (ℕ.suc n)) ∎
        where open ≤-Reasoning
    
    private
        safe-tail : ∀ {A : Set} → (l : List A) → {n : ℕ} → length l ℕ.≥ ℕ.suc n → List A
        safe-tail (x ∷ l) ≥2 = l

        Pairs : {A : Set} → (l : List A) → length l ℕ.≥ 2 → List (A × A)
        Pairs l length≥2 = Data.List.zipWith (λ x y → x , y) l (safe-tail l length≥2)
        
        ∀Pairs : {A : Set} → (f : A → A → Set) → (l : List A) → length l ℕ.≥ 2 → Set
        ∀Pairs f l length≥2 = All (λ pair → uncurry f pair) (Pairs l length≥2)

        Fₙ-Pairs : ∀ (z : ℤ) (n : ℕ) → List (F × F)
        Fₙ-Pairs z n = Pairs (Fₙ z n) (Fₙlength≥2 z n)

        ∀Fₙ-Pairs : ∀ (z : ℤ) (n : ℕ) → (f : F → F → Set) → Set
        ∀Fₙ-Pairs z n f = All (λ pair → uncurry f pair) (Fₙ-Pairs z n)

        -- test : ∀ (z : ℤ) (n : ℕ) → (f : F → F → Set) → ∀Pairs f ()
        -- test = {!   !}

        indStep : ∀ (z : ℤ) (n : ℕ) → (pred : F → F → Set) →
            (hyp : ∀Fₙ-Pairs z n pred) →  
            (∀ {x y : F} → (pair∈Fₙ : ( x , y ) ∈ₚ (Fₙ-Pairs z n)) → (pair-pred : pred x y) → hyp [ pair∈Fₙ ]= pair-pred → F.d x ℕ.+ F.d y ℕ.≥ n → (pred x ((F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y))) × (pred ((F.n x ℤ.+ F.n y) / (F.d x ℕ.+ F.d y)) y)) → 
            ∀Fₙ-Pairs z (ℕ.suc n) pred
        indStep z n f hyp with Fₙ-Pairs z (ℕ.suc n)
        ... | fₙ+1 = {! hyp !} 

        sucz-z≡1 : ∀ (z : ℤ) → ℤ.suc z ℤ.- z ≡ ℤ.1ℤ
        sucz-z≡1 (ℤ.+_ ℕ.zero) = refl
        sucz-z≡1 (ℤ.+_ (ℕ.suc n)) = begin
            ℤ.suc (ℤ.+ ℕ.suc n) ℤ.- ℤ.+ ℕ.suc n ≡⟨ {! refl  !} ⟩
            (ℤ.+ ℕ.suc n) ℤ.- ℤ.+ n ≡⟨ {! refl  !} ⟩
            ℤ.1ℤ ∎
            where open ≡-Reasoning 
        sucz-z≡1 (ℤ.negsuc n) = {!   !}        

    qn-pm=1 : ∀ (z : ℤ) (n : ℕ) → ∀Fₙ-Pairs z n λ x y → (F.n y ℤ.* (ℤ.+ (F.d x))) ℤ.- (F.n x ℤ.* (ℤ.+ (F.d y))) ≡ ℤ.+ 1
    qn-pm=1 z ℕ.zero = (begin 
        ℤ.suc z ℤ.* ℤ.+ 1 ℤ.- z ℤ.* ℤ.1ℤ ≡⟨ cong (λ x → ℤ.suc z ℤ.* ℤ.+ 1 ℤ.- x) (ℤProp.*-identityʳ z) ⟩
        ℤ.suc z ℤ.* ℤ.+ 1 ℤ.- z ≡⟨ cong (λ x → x ℤ.- z) (ℤProp.*-identityʳ (ℤ.suc z)) ⟩
        ℤ.suc z ℤ.- z ≡⟨ sucz-z≡1 z ⟩
        ℤ.+ 1 ∎) ∷ []
        where open ≡-Reasoning
    qn-pm=1 z (ℕ.suc n) with qn-pm=1 z n
    ...  | indHyp = {!   !} 
    --}