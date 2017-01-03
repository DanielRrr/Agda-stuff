module PropCalc where

Prop : Set₁
Prop = Set

data ⊤ : Prop where
  true : ⊤

data ⊥ : Prop where

elim⊥ : {A : Prop} → ⊥ → A
elim⊥()

infixr 0 _⇒_
_⇒_ : Prop → Prop → Prop
P ⇒ Q = P → Q

data _∨_ (P Q : Prop) : Prop where
  intro∨₁ : P → P ∨ Q
  intro∨₂ : Q → P ∨ Q

elim∨ : {P Q R : Prop} → (P ⇒ R) ⇒ (Q ⇒ R) ⇒ (P ∨ Q ⇒ R)
elim∨ p⇒r q⇒r (intro∨₁ p) = p⇒r p
elim∨ p⇒r q⇒r (intro∨₂ q) = q⇒r q

infixr 1 _∨_

data _∧_ (P Q : Prop) : Prop where
  _,_ : P → Q → P ∧ Q

infixr 2 _∧_

elim∧₁ : {A B : Prop} → A ∧ B ⇒ A
elim∧₁ (x , y) = x

elim∧₂ : {A B : Prop} → A ∧ B ⇒ B
elim∧₂ (x , y) = y

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

residual₁ : {P Q R : Prop} → (P ⇒ Q ⇒ R) ⇒ P ∧ Q ⇒ R
residual₁ p⇒q⇒r p∧q = p⇒q⇒r (elim∧₁ p∧q) (elim∧₂ p∧q)

residual₂ : {P Q R : Prop} → (P ∧ Q ⇒ R) ⇒ P ⇒ Q ⇒ R
residual₂ p∧q⇒r p q = p∧q⇒r (p , q)
