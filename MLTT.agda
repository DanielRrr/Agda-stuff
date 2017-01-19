module MLTT where

id : {A : Set} → A → A
id = λ x → x

K : {A : Set} → {B : A → Set} → (x : A) → B x → A
K x y = x

S : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set}
  → (g : (x : A) → (y : B x) → C x y)
  → (f : (x : A) → B x)
  → (x : A)
  → C x (f x)
S g f x = g x (f x) 

record Σ (A : Set) (P : A → Set) : Set where  
  constructor _,_
  field
    π₁ : A       
    π₂ : P (π₁)  
open Σ public

fst : {A : Set}{B : A → Set} → Σ A B → A
fst (π₃ , π₄) = π₃

curry : {A : Set} {B : A → Set} {C : Σ A B → Set }
  → (∀ s → C s) → (∀ x y → C (x , y))
curry f x y = f (x , y)

uncurry : {A : Set} → {B : A → Set} → {C : Σ A B → Set} → ((x : A) → (y : B x) → C (x , y)) → (z : Σ A B) → C z
uncurry f (a , x) = f a x

_×_ : (A : Set)(B : Set) → Set
A × B = Σ A (λ _ → B)

Π : (A : Set)(B : A → Set) → Set
Π A B = (x : A) → B x


ap : {A : Set} {B : A → Set} → Π A B → (a : A) → B a
ap f x = f x

_∘_ : {A : Set} {B : A → Set} {C : (a : A) → (B a → Set)} → (f : {a : A} → Π (B a) (C a)) → (g : Π A B) → Π A (λ a → C a (g a))
f ∘ g = λ x → f (g x)

data Id (A : Set) : A → A → Set where
  r : {a : A} → Id A a a

J : {A : Set} → {a b : A} → {C : (x y : A) → (z : Id A x y) → Set} → ({x : A} → C x x r) → (c : Id A a b) → C a b c
J d r = d

