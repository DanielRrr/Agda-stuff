module AdvancedIntro where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
true or y = true
false or y = y

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

_+_ : Nat → Nat → Nat
zero + y = y
succ x + y = succ (x + y)

_*_ : Nat → Nat → Nat
zero * y = zero
succ x * y = x + (x * y)

identity : (A : Set) → A → A
identity A x = x

apply : (A : Set)(B : A → Set) → ((x : A) → B x) → (a : A) → B a
apply A B f a = f a

identity₂ : (A : Set) → A → A
identity₂ = \A x → x

id : {A : Set} → A → A
id x = x

_∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}(f : {x : A}(y : B x) → C x y)(g : (x : A) → B x)(x : A) → C x (g x)
(f ∘ g) x = f (g x)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

head : {A : Set}{n : Nat} → Vec A (succ n) → A
head (x :: xs) = x

vmap : {A B : Set}{n : Nat} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data Image_∋_ {A B : Set}(f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

inv : {A B : Set}(f : A → B)(y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (succ n)
  fsux : {n : Nat} → Fin n → Fin (succ n)

magic : {A : Set} → Fin zero → A
magic ()

_!_ : {n : Nat}{A : Set} → Vec A n → Fin n → A
[] ! ()
(x :: v) ! fzero = x
(x :: v) ! fsux A₁ = v ! A₁

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool → Set
isTrue true = True
isTrue false = False

_<_ : Nat → Nat → Bool
zero < zero = false
zero < succ y = true
succ x < zero = false
succ x < succ y = x < y

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

length : {A : Set} → List A → Nat
length Nil = zero
length (Cons x xs) = succ (length xs)

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

data _≤_ : Nat → Nat → Set where
  leq-zero : {n : Nat} → zero ≤ n
  leq-succ : {m n : Nat} → m ≤ n → succ m ≤ succ n

leq-trans : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-succ p) (leq-succ q) = leq-succ (leq-trans p q)

min : Nat → Nat → Nat
min x y with x < y
min x y | true = x
min x y | false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter p Nil = Nil
filter p (Cons x xs) with p x
... | true = Cons x (filter p xs)
... | false = filter p xs

data _≠_ : Nat → Nat → Set where
  z≠s : {n : Nat} → zero ≠ succ n
  s≠z : {n : Nat} → succ n ≠ zero
  s≠s : {m n : Nat} → succ m ≠ succ n

data Equal? (n m : Nat) : Set where
  eq : n == m → Equal? n m
  neq : n ≠ m → Equal? n m

equal? : (n m : Nat) → Equal? n m
equal? zero zero = eq refl
equal? zero (succ y) = neq z≠s
equal? (succ n) zero = neq s≠z
equal? (succ x) (succ y) with equal? x y
equal? (succ x) (succ .x) | eq refl = eq refl
equal? (succ x) (succ y) | neq p = neq ((s≠s))

infix 20 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  stop : Nil ⊆ Nil
  drop : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ Cons y ys
  keep : ∀ {x xs ys} → xs ⊆ ys → Cons x xs ⊆ Cons x ys

lem-filter : {A : Set}(p : A → Bool)(xs : List A) → filter p xs ⊆ xs
lem-filter p Nil = stop
lem-filter p (Cons x xs) with p x
... | true = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)

infix 25 _==_
infixr 40 _+_

lem-plus-zero : (n : Nat) → n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (succ n) with n + zero | lem-plus-zero n
... | .n | refl = refl

module M where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

maybe : {A B : Set} → B → (A → B) → M.Maybe A → B
maybe z f M.nothing = z
maybe z f (M.just x) = f x

mapMaybe : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
mapMaybe f M.nothing = M.nothing
mapMaybe f (M.just x) = M.just (f x)

module Sort (A : Set)(_<_ : A → A → Bool) where
  insert : A → List A → List A
  insert y Nil = Cons y Nil
  insert y (Cons x xs) with x < y
  ... | true = Cons x (insert y xs)
  ... | false = Cons y (Cons x xs)

  sort : List A → List A
  sort Nil = Nil
  sort (Cons x xs)  = insert x (sort xs)
