module Functors where

data Functor : Set₁ where
  |Id| : Functor
  |K| : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|×|_ : Functor → Functor → Functor

data _⊕_ (A B : Set) : Set where
  in₁ : A → A ⊕ B
  in₂ : B → A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 50 _|+|_ _⊕_
infixr 60 _|×|_ _×_

[_] : Functor → Set → Set
[ |Id| ] X = X
[ |K| A  ] X  = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |×| G ] X = [ F ] X × [ G ] X

map : (F : Functor){X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
map |Id| f x = f x
map (|K| A) f c = c
map (F |+| G) f (in₁ x) = in₁ (map F f x)
map (F |+| G) f (in₂ y) = in₂ (map G f y)
map (F |×| G) f (x , y) = map F f x , map G f y

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) → μ F

mapFold : ∀ {X} F G → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
mapFold |Id| G φ  < x > = φ (mapFold G G φ x)
mapFold (|K| A) G φ c = c
mapFold (F |+| G) F₁ φ (in₁ x) = in₁ (mapFold F F₁ φ x)
mapFold (F |+| G) F₁ φ (in₂ y) = in₂ (mapFold G F₁ φ y)
mapFold (F |×| G) F₁ φ (x , y) = mapFold F F₁ φ x , mapFold G F₁ φ y 

fold : {F : Functor}{A : Set} → ([ F ] A → A) → μ F → A
fold {F} φ < x > = φ (mapFold F F φ x)

data Bool : Set where
  false : Bool
  true  : Bool
  
data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool → Set
isTrue true = True
isTrue false = False

NatF = |K| True |+| |Id|
NAT = μ NatF

Z : NAT
Z = < in₁ _ >

S : NAT → NAT
S n = < in₂ n >

ListF = λ A → |K| True |+| |K| A |×| |Id|
LIST = λ A → μ (ListF A)

nil : {A : Set} → LIST A
nil = < in₁ _ >

cons : {A : Set} → A → LIST A → LIST A
cons x xs = < in₂ (x , xs) >

[_||_] : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
[ f || g ] (in₁ x) = f x
[ f || g ] (in₂ y) = g y

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (x , y) = f x y

const : {A B : Set}  → A → B → A
const x y = x

foldr : {A B : Set} → (A → B → B) → B → LIST A → B
foldr {A}{B} f z = fold [ const z || uncurry f ]

plus : NAT → NAT → NAT
plus n m = fold [ const m || S ] n
