module Dave.Base.Maybe where
    open import Agda.Primitive

    private
        variable
            ℓ-A ℓ-B : Level
            A : Set ℓ-A
            B : Set ℓ-B

    data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
        just : A → Maybe A
        nothing : Maybe A

    infixl 1 _>>=Maybe_
    _>>=Maybe_ : Maybe A → (A → Maybe B) → Maybe B
    nothing >>=Maybe f = nothing
    just a  >>=Maybe f = f a
   

        