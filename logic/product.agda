module logic.product where

    data _×_ (A B : Set) : Set where
        _,_ : A → B → A × B

    proj₁ : {A B : Set} → A × B → A
    proj₁ (a , b) = a

    proj₂ : {A B : Set} → A × B → B
    proj₂ (a , b) = b