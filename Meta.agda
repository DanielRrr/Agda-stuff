module Meta where

_∘_ : ∀ {α β γ} → {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ} → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

zip : {A B : Set} → List A → List B → List (A × B)
zip Nil Nil = Nil
zip Nil (Cons x b) = Nil
zip (Cons x a) Nil = Nil
zip (Cons x a) (Cons x₁ b) = Cons (x , x₁) (zip a b)

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

length : {A : Set} → List A → ℕ
length Nil = Z
length (Cons x x₁) = S (length x₁)

data Vector (A : Set) : ℕ → Set where
  [] : Vector A Z
  _::_ : {n : ℕ} → A → Vector A n → Vector A (S n)

vapp : ∀ {n A B} → Vector (A → B) n → Vector A n → Vector B n
vapp [] xs = []
vapp (f :: fs) (x :: xs) = f x :: vapp fs xs

record EndoFunctor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
open EndoFunctor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _<*>_
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record {fmap = _<*>_ ∘ pure}
open Applicative {{...}} public

vec : ∀ {n A} → A → Vector A n
vec {Z} x = []
vec {S n} x = x :: vec {n} x

applicativeVec : ∀ {n} → Applicative λ A → Vector A n
applicativeVec = record {pure = vec; _<*>_ = vapp}

applicativeFun : ∀ {S} → Applicative λ X → S → X
applicativeFun = record
  {pure = λ x y → x
  ;_<*>_ = λ f g x → (f x) (g x)
  }

record Monad (F : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → F A
    _>>=_  : ∀ {A B} → F A → (A → F B) → F B
  monadApplicative : Applicative F
  monadApplicative = record
    {pure  = return
    ;_<*>_ = λ ff fs → ff >>= λ f → fs >>= λ s → return (f s)
    }
open Monad {{...}} public

_+_ : ℕ → ℕ → ℕ
Z + b = b
S a + b = S (a + b)

tail : ∀ {n A} → Vector A (S n) → Vector A n
tail (x :: x₁) = x₁

record Monoid (A : Set) : Set where
  infixr 4 _●_
  field
    ε : A
    _●_ : A → A → A
  monoidApplicative : Applicative λ _ → A
  monoidApplicative = record
    { pure = λ _ → ε
    ; _<*>_ = _●_
    }
open Monoid {{...}} public

instance
  natMonoid : Monoid ℕ
  natMonoid = record { ε = Z; _●_ = _+_}

infix 4 _≡_
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

cong : {A B : Set}{a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

record MonoidSatisfies A {{M : Monoid A}} : Set where
  field
    leftOne  : (a : A)     → (ε ● a) ≡ a
    rightOne : (a : A)     → (a ● ε) ≡ a
    assoc    : (a b c : A) → ((a ● b) ● c) ≡ (a ● (b ● c))
open MonoidSatisfies {{...}} public

leftOneNat : (n : ℕ) → (Z + n) ≡ n
leftOneNat n = refl

rightOneNat : (n : ℕ) → (n + Z) ≡ n
rightOneNat Z = refl
rightOneNat (S n) = cong S (rightOneNat n)

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc Z y z = refl
+-assoc (S x) y z = cong S (+-assoc x y z)

NatMonoidSatisfies : MonoidSatisfies ℕ
NatMonoidSatisfies = record {leftOne = leftOneNat; rightOne = rightOneNat; assoc = +-assoc}

_++_ : {A : Set} → List A → List A → List A
Nil ++ y = y
Cons x x₁ ++ y = Cons x (x₁ ++ y)

instance
  monoidList : {A : Set} → Monoid (List A)
  monoidList = record {ε = Nil; _●_ = _++_}

addNilLeft : {A : Set}(xs : List A) → Nil ++ xs ≡ xs
addNilLeft xs = refl

addNilRight : {A : Set}(xs : List A) → xs ++ Nil ≡ xs
addNilRight Nil = refl
addNilRight (Cons x xs) = cong (Cons x) (addNilRight xs)

++-assoc : {A : Set}(xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc Nil ys zs = refl
++-assoc (Cons x xs) ys zs = cong (Cons x) (++-assoc xs ys zs)

ListMonoidSatisfies : {A : Set} → MonoidSatisfies (List A)
ListMonoidSatisfies =
  record
  { leftOne = addNilLeft
  ; rightOne = addNilRight
  ; assoc = ++-assoc }
