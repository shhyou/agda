{-# OPTIONS --prop #-}
module _ where
open import Agda.Primitive using (Set; Prop)

data _≡_ {A : Set} (a : A) : A -> Set where
    refl : a ≡ a

data Bool : Set where
    false true : Bool

escape : ∀ {b1 b2 : Bool} -> .(b1 ≡ b2) -> b1 ≡ b2
escape {false} {false} _ = refl
escape {true}  {true} _ = refl
