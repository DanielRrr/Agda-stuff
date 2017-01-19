module MLTT where

id : {A : Set} → A → A
id = λ x → x

K : {A : Set} → {B : A → Set} → (x : A) → B x → A
K x y = x

S : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → (g : (x : A) → (y : B x) → C x y)
  → (f : (x : A) → B x)
  → (x : A)
  → C x (f x)
S g f x = g x (f x) 

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

fst : {A : Set} → {P : A → Set} → Σ A P → A
fst (a , x) = a

curry : {A : Set} → {B : A → Set} → {C : Σ A B → Set} → ((x : A) → (y : B x) → C (x , y)) → (z : Σ A B) → C z
curry f (a , x) = f a x

data Π (A : Set) (B : A → Set) : Set where
  Λ : ((a : A) → B a) → Π A B

ap : {A : Set} → {B : A → Set} → (a : A) → Π A B → B a
ap x (Λ x₁) = x₁ x

data Id (A : Set) : A → A → Set where
  r : {a : A} → Id A a a

J : {A : Set} → {a b : A} → {C : (x y : A) → (z : Id A x y) → Set} → ({x : A} → C x x r) → (c : Id A a b) → C a b c
J d r = d
