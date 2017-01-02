module PropCalc where

Prop : Set₁
Prop = Set

infixr 0 _⇒_
_⇒_ : Prop → Prop → Prop
P ⇒ Q = P → Q

data _∨_ (P Q : Prop) : Prop where
  inl : P → P ∨ Q
  inr : Q → P ∨ Q

infixr 1 _∨_

data _∧_ (P Q : Prop) : Prop where
  _,_ : P → Q → P ∧ Q

infixr 2 _∧_

_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

infixr 0 _⇔_

K : {P Q : Prop} → P ⇒ Q ⇒ P
K p q = p

S : {P Q R : Prop} → (P ⇒ Q ⇒ R) ⇒ (P ⇒ Q) ⇒ P ⇒ R
S x y z = (x z) (y z)

I : {P : Prop} → P ⇒ P
I p = p

flip : {P Q R : Prop} → (P ⇒ Q ⇒ R) ⇒ Q ⇒ P ⇒ R
flip = λ x y z → x z y

infixr 9 _∘_
_∘_ : {P Q R : Prop} → (Q ⇒ R) ⇒ (P ⇒ Q) ⇒ P ⇒ R
(x ∘ y) z = x (y z)

infixr 9 _∘₁_
_∘₁_ : {P Q R : Prop} → (P ⇒ Q) ⇒ (Q ⇒ R) ⇒ P ⇒ R
(x ∘₁ y) z = y (x z)
