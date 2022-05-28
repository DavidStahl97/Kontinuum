module Dave.Algebra.Naturals.Definition where
  open import Dave.Equality public
  open import Dave.Logic.Basics
  open import Dave.Structures.Monoid public
  
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  one = suc zero
  two = suc one
  three = suc two
  four = suc three
  five = suc four
  six = suc five
  seven = suc six
  eight = suc seven
  nine = suc eight

  {-# BUILTIN NATURAL  ℕ #-} 

  ℕ-suc-≡ : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
  ℕ-suc-≡ refl = refl

  suc≡→≡ : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
  suc≡→≡ refl = refl

  ℕ-suc-≠ : ∀ {m n : ℕ} → m ≠ n → suc m ≠ suc n
  ℕ-suc-≠ m≠n suc-≡ = m≠n (suc≡→≡ suc-≡)