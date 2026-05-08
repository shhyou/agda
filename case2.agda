{-# OPTIONS --safe --without-K --prop #-}

module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Data.Empty
open import Data.Fin.Base

data ⊥ₚ : Prop where

data [_]s (A : Set) : Prop where
  squash : A → [ A ]s

mapCongPred : {m n : Nat} → [ suc m ≡ suc n ]s → [ m ≡ n ]s
mapCongPred (squash refl) = squash refl

squashAbsurd : {A : Set} → (A → ⊥) → [ A ]s → ⊥ₚ
squashAbsurd ¬A (squash a) with () ← ¬A a

contradictionₚ : {A B : Set} → [ A ]s → (A → ⊥) → B
contradictionₚ [A] ¬A with () ← squashAbsurd ¬A [A]

castp : ∀ {m n} → [ m ≡ n ]s  → Fin m → Fin n
castp {zero}  {zero}  m≡n fm       = fm
castp {zero}  {suc n} (squash ())
castp {suc m} {suc n} m≡n zero     = zero
castp {suc m} {suc n} m≡n (suc fm) = suc (castp (mapCongPred m≡n) fm)
