module first where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

and : Bool → Bool → Bool
and true true = true
and true false = false
and false true = false
and false false = false

or : Bool → Bool → Bool
or true true = true
or true false = true
or false true = true
or false false = false

imply : Bool → Bool → Bool
imply true true = true
imply true false = false
imply false true = true
imply false false = true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

add : Nat → Nat → Nat
add zero y = y
add (succ x) y = succ (add x y)

_+_ : Nat → Nat → Nat
zero + b = b
succ a + b = succ (a + b)

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

length : {A : Set} → List A → Nat
length Nil = zero
length (Cons x l) = succ (length l)

map : {A B : Set} → (A → B) → List A → List B
map f Nil = Nil
map f (Cons x x₁) = Cons (f x) (map f x₁)

concat : {A : Set} → List A → List A → List A
concat Nil m = Nil
concat (Cons x l) m = Cons x (concat l m)

data Vector (A : Set) : Nat → Set where
  Empty : Vector A zero
  VHead : {n : Nat} → A → Vector A n → Vector A (succ n)

vLength : {A : Set} → {n : Nat} → Vector A n → Nat
vLength {A} {zero} v = zero
vLength {A} {succ n} v = succ n

vMap : {A B : Set} → {n : Nat} → (A → B) → Vector A n → Vector B n
vMap f Empty = Empty
vMap f (VHead x v) = VHead (f x) (vMap f v)

vConcat : {A : Set} → {n m : Nat} → Vector A n → Vector A m → Vector A (n + m)
vConcat Empty w = w
vConcat (VHead x v) w = VHead x (vConcat v w)
