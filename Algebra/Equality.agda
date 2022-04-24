module Algebra.Equality where
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  infix 4 _≡_
  
  {-# BUILTIN EQUALITY _≡_ #-}

  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl b = b

  cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
    → u ≡ x
    → v ≡ y
    → f u v ≡ f x y
  cong₂ f refl refl = refl

  cong-app : ∀ {A B : Set} {f g : A → B}
    → f ≡ g
    → ∀ (x : A) → f x ≡ g x
  cong-app refl x = refl

  subst : ∀ {A : Set} {x y : A} (P : A → Set)
    → x ≡ y
    → P x → P y
  subst P refl px = px  

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {A : Set} {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ {A : Set} (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ {A : Set} (x : A)
     -----
     → x ≡ x
  x ∎  =  refl  