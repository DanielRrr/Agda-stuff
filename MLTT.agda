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

snd : {A : Set}{B : A → Set}(p : Σ A B) → B (π₁ p) 
snd (π₃ , π₄) = π₄

curry : {A : Set} {B : A → Set} {C : Σ A B → Set } → (∀ s → C s) → (∀ x y → C (x , y))
curry f x y = f (x , y)

uncurry : {A : Set} → {B : A → Set} → {C : Σ A B → Set} → ((x : A) → (y : B x) → C (x , y)) → (z : Σ A B) → C z
uncurry f (a , x) = f a x

_×_ : (A : Set)(B : Set) → Set
A × B = Σ A (λ _ → B)

curry₁ : {A B C : Set} → (A × B → C) → A → B → C
curry₁ = curry

uncurry₁ : {A B C : Set} → (A → B → C) → A × B → C
uncurry₁ = uncurry

Π : (A : Set)(B : A → Set) → Set
Π A B = (x : A) → B x

ap : {A : Set} {B : A → Set} → Π A B → (a : A) → B a
ap f x = f x

_$_ : {A B : Set} → (A → B) → A → B
f $ x = ap f x

_∘_ : {A : Set} {B : A → Set} {C : (a : A) → (B a → Set)} → (f : {a : A} → Π (B a) (C a)) → (g : Π A B) → Π A (λ a → C a (g a))
f ∘ g = λ x → f (g x)

_∘₁_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘₁ g = f ∘ g

data Id (A : Set) : A → A → Set where
  r : {a : A} → Id A a a

J : {A : Set} → {a b : A} → {C : (x y : A) → (z : Id A x y) → Set} → ({x : A} → C x x r) → (c : Id A a b) → C a b c
J d r = d

Pi-Sigma : {A : Set}{P : A → Set} → Π A P → (x : A) → Σ A P  
Pi-Sigma f x = x , (f x)

sym : {A : Set} → {a b : A} → Id A a b → Id A b a
sym r = r

trans : {A : Set} → {a b c : A} → Id A a b → Id A b c → Id A a c
trans r r  = r

cong : {A : Set} → {a b : A} → {B : Set} → {f : A → B} → Id A a b → Id B (f a) (f b)
cong r = r

Id-S : {A : Set} → {P : A → Set} → {f : Π A P} → {a b : A} → Id A a b → Id (Σ A P) (a , f a) (b , f b) 
Id-S r = r

InDis : {A : Set} → {C : A → Set} → (x y : A) → Id A x y → C x → C y
InDis x y r f = f


data Two : Set where
  0₂ : Two
  1₂ : Two

rec₂ : (A : Set) → (a : A) → (b : A) → Two → A
rec₂ A x y 0₂ = x
rec₂ A x y 1₂ = y

ind₂ : (f : Two → Set) → f (0₂) → f (1₂) → Π Two f
ind₂ f x y 0₂ = x
ind₂ f x y 1₂ = y

data ℕ : Set where
  Z : ℕ
  suc : ℕ → ℕ 

recNat : (A : Set) → A → (ℕ → A → A) → ℕ → A
recNat A x f Z = x
recNat A x f (suc n) = f n (recNat A x f n)

indNat : (C : ℕ → Set) → C Z → ((x : ℕ) → C x → C (suc x)) → Π ℕ C
indNat C c₀ c₁ Z = c₀
indNat C c₀ f (suc n) = f n (indNat C c₀ f n)
