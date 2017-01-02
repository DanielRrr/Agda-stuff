module Cumulative where

open import Data.Nat
open import Data.List
open import Data.Bool

data Type : Set where
  bool : Type
  nat : Type
  list : Type → Type
  pair : Type → Type → Type

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 60 _×_

El : Type → Set
El nat = ℕ
El bool = Bool
El (list a) = List (El a)
El (pair a b) = El a × El b

infix 30 _≡_
_≡_ : {a : Type} → El a → El a → Bool
_≡_ {bool} false y = not y
_≡_ {bool} true y = y
_≡_ {nat} zero zero = true
_≡_ {nat} zero (suc y) = false
_≡_ {nat} (suc x) zero = false
_≡_ {nat} (suc x) (suc y) = x ≡ y
_≡_ {list a} [] [] = true
_≡_ {list a} [] (x ∷ y) = false
_≡_ {list a} (x ∷ x₁) [] = false
_≡_ {list a} (x ∷ xs) (y ∷ ys) = (x ≡ y) ∧ (xs ≡ ys)
_≡_ {pair a a₁} (x₁ , y₁) (x₂ , y₂) = (x₁ ≡ x₂) ∧ (y₁ ≡ y₂)
