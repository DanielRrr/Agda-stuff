module Views where

open import Data.Nat
open import Data.List
open import Data.Bool

module Function where
  infixl 0 _$_
  _$_ : ∀ {α β} → {A : Set α}{B : A → Set β} → (f : (x : A) → B x) → ((x : A) → B x)
  f $ x = f x

  infixl 0 _$'_
  _$'_ : ∀ {α β} → {A : Set α}{B : Set β} → (A → B) → A → B
  f $' x = f $ x

  _∘_ : ∀ {α β γ} → {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ} → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  _∘'_ : ∀ {α β γ} → {A : Set α} {B : Set β} {C : Set γ} → (B → C) → (A → B) → A → C
  f ∘' g = f ∘ g

  flip : ∀ {α β γ} → {A : Set α}{B : Set β}{C : A → B → Set γ} → ((x : A) → (y : B) → C x y) → ((y : B) → (x : A) → C x y)
  flip f x y = f y x

  id : ∀ {α} {A : Set α} → A → A
  id x = x

  const : ∀ {α β} → {A : Set α}{B : Set β} → (A → B → A)
  const = λ x y → x

open Function public
  
data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity 0 = even 0
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)

half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(1 + k * 2) | odd k = k
 
infixr 30 _:all:_
data All {A : Set}(P : A → Set) : List A → Set where
  all[] : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool → Set
isTrue true = True
isTrue false = False

satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = isTrue (p x)

isFalse : Bool → Set
isFalse = satisfies not

data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs → Find p xs

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x
  
data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x ==  y → Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} → x == true → isTrue x
trueIsTrue refl = _

falseIsFalse : {x : Bool} → x == false → isFalse x
falseIsFalse refl = _

find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with inspect (p x)
... | it true prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x ∷ ._) | it false _ | found xs y py ys =
  found (x ∷ xs) y py ys
find p (x ∷ xs) | it false prf | not-found npxs =
  not-found (falseIsFalse prf :all: npxs)

data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs} → x ∈ (x ∷ xs)
  tl : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A}{x : A}{xs} → x ∈ xs → ℕ
index hd = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside : (x : A) (p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

infixr 30 _⇒_
data Type : Set where
  ₁ : Type
  _⇒_ : Type → Type → Type

data Equal? : Type → Type → Set  where
  yes : ∀ {τ} → Equal? τ τ
  no : ∀ {σ τ} → Equal? σ τ

_=?=_ : (σ τ : Type) → Equal? σ τ
₁ =?= ₁  = yes
₁ =?= (_ ⇒ _) = no
(_ ⇒ _) =?= ₁ = no
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(σ ⇒ τ) =?= (.σ ⇒ .τ) | yes | yes = yes
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) | _ | _ = no

infixl 80 _$$_

data Raw : Set where
  var  : ℕ → Raw
  _$$_ : Raw → Raw → Raw
  lam  : Type → Raw → Raw

Ctx = List Type

data Term (Γ : Ctx) : Type → Set where
  var  : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam  : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

wear : ∀ {Γ τ}  → Term Γ τ → Raw
wear (var x) = var (index x)
wear (t $$ y) = wear t $$ wear y
wear (lam σ t) = lam σ (wear t)

data Infer (Γ : Ctx) : Raw → Set where
  ok      : (τ : Type)(t : Term Γ τ) → Infer Γ (wear t)
  bad     : {e : Raw} → Infer Γ e

_!_ : {A : Set}(xs : List A)(n : ℕ) -> Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p) | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + n) | outside n = outside n

infer : (Γ : Ctx)(e : Raw) -> Infer Γ e
infer Γ (var n) with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = bad
infer Γ (var .(index x)) | inside σ x = ok σ (var x)
infer Γ (e1 $$ e2) with infer Γ e1
infer Γ (e1 $$ e2) | bad = bad
infer Γ (.(wear t1) $$ e2) | ok ₁ t1 = bad
infer Γ (.(wear t1) $$ e2) | ok (σ ⇒ τ) t1 with infer Γ e2
infer Γ (.(wear t1) $$ e2) | ok (σ ⇒ τ) t1 | bad = bad
infer Γ (.(wear t1) $$ .(wear t2)) | ok (σ ⇒ τ) t1 | ok σ’ t2 with σ =?= σ’
infer Γ (.(wear t1) $$ .(wear t2)) | ok (σ ⇒ τ) t1 | ok .σ t2 | yes = ok τ (t1 $$ t2)
infer Γ (.(wear t1) $$ .(wear t2)) | ok (σ ⇒ τ) t1 | ok σ’ t2 | no = bad
infer Γ (lam σ e) with infer (σ ∷ Γ) e
infer Γ (lam σ .(wear t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ e) | bad = bad
