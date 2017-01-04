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

const : {P Q : Prop} → P ⇒ Q ⇒ P
const p q = p

S : {P Q R : Prop} → (P ⇒ Q ⇒ R) ⇒ (P ⇒ Q) ⇒ P ⇒ R
S x y z = (x z) (y z)

I : {P : Prop} → P ⇒ P
I p = p

flip : {P Q R : Prop} → (P ⇒ Q ⇒ R) ⇒ Q ⇒ P ⇒ R
flip = λ x y z → x z y

dubl : {P Q : Prop} → (P ⇒ P ⇒ Q) ⇒ P ⇒ Q
dubl p⇒p⇒q p = p⇒p⇒q p p

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

∧-comm₁ : {P Q : Prop} → P ∧ Q ⇒ Q ∧ P
∧-comm₁ (x , y) = (y , x)

∧-comm₂ : {P Q : Prop} → Q ∧ P ⇒ P ∧ Q
∧-comm₂ (x , y) = (y , x)

∧-comm : {P Q : Prop} → P ∧ Q ⇔ Q ∧ P
∧-comm = (∧-comm₁ , ∧-comm₂)

∧-assoc₁ : {P Q R : Prop} → (P ∧ Q) ∧ R ⇒ P ∧ (Q ∧ R)
∧-assoc₁ ((x , y) , z) = (x , (y , z))

∧-assoc₂ : {P Q R : Prop} → P ∧ (Q ∧ R) ⇒ (P ∧ Q) ∧ R
∧-assoc₂ (x , (y , z)) = ((x , y) , z)

∧-assoc : {P Q R : Prop} → (P ∧ Q) ∧ R ⇔ P ∧ (Q ∧ R)
∧-assoc = (∧-assoc₁ , ∧-assoc₂)

∧-apply : {P Q : Prop} → P ∧ (P ⇒ Q) ⇒ Q
∧-apply (p , p⇒q)  = elim∧₂ (p , p⇒q) (elim∧₁ (p , p⇒q))

apply-∧ : {P Q : Prop} → (P ⇒ Q) ∧ P ⇒ Q
apply-∧ (p⇒q , p) = elim∧₁ (p⇒q , p) (elim∧₂ (p⇒q , p))

imdepotency₁ : {P : Prop} → (P ∧ P) ⇒ P
imdepotency₁ p∧p = elim∧₁ p∧p

imdepotency₂ : {P : Prop} → P ⇒ (P ∧ P)
imdepotency₂ p = (p , p)

imdepotency : {P : Prop} → (P ∧ P) ⇔ P
imdepotency = (imdepotency₁ , imdepotency₂)

transitivity : {P Q R : Prop} → (P ⇒ Q) ∧ (Q ⇒ R) ⇒ P ⇒ R
transitivity ((p⇒q) , (q⇒r)) p = elim∧₂ ((p⇒q) , (q⇒r)) (elim∧₁ ((p⇒q) , (q⇒r)) p)

∨-comm₁ : {P Q : Prop} → (P ∨ Q) ⇒ (Q ∨ P)
∨-comm₁ (intro∨₁ p) = intro∨₂ p
∨-comm₁ (intro∨₂ q) = intro∨₁ q

v-comm₂ : {P Q : Prop} → (Q ∨ P) ⇒ (P ∨ Q)
v-comm₂ (intro∨₁ x) = intro∨₂ x
v-comm₂ (intro∨₂ x) = intro∨₁ x

∨-comm : {P Q : Prop} → (P ∨ Q) ⇔ (Q ∨ P)
∨-comm = (∨-comm₁ , v-comm₂)

∨-assoc₁ : {P Q R : Prop} → P ∨ (Q ∨ R) ⇒ (P ∨ Q) ∨ R
∨-assoc₁ (intro∨₁ x) = intro∨₁ (intro∨₁ x)
∨-assoc₁ (intro∨₂ (intro∨₁ x)) = intro∨₁ (intro∨₂ x)
∨-assoc₁ (intro∨₂ (intro∨₂ x)) = intro∨₂ x

∨-assoc₂ : {P Q R : Prop} → (P ∨ Q) ∨ R ⇒ P ∨ (Q ∨ R)
∨-assoc₂ (intro∨₁ (intro∨₁ x)) = intro∨₁ x
∨-assoc₂ (intro∨₁ (intro∨₂ x)) = intro∨₂ (intro∨₁ x)
∨-assoc₂ (intro∨₂ x) = intro∨₂ (intro∨₂ x)

∨-assoc : {P Q R : Prop} → P ∨ (Q ∨ R) ⇔ (P ∨ Q) ∨ R
∨-assoc = (∨-assoc₁ , ∨-assoc₂)

deMorgan : {A B : Prop} → ¬(A ∨ B) ⇒ ((¬ A) ∧ (¬ B))  
deMorgan = (λ f → (λ x → f (intro∨₁ x)) , (λ x → f (intro∨₂ x)))

contradiction : {A B : Prop} → A ⇒ (¬ A ⇒ B)
contradiction x ¬x = elim⊥(¬x x)

contraposition : {A B : Prop} → (A ⇒ B) ⇒ (¬ B ⇒ ¬ A)
contraposition = flip _∘_

contraposition¬ : {A B : Prop} → (A ⇒ ¬ B) ⇒ (B ⇒ ¬ A)
contraposition¬ = flip

double : {A : Prop} → A ⇒ ¬ (¬ A)
double = contradiction

brower : {A : Prop} → ¬ (¬ (¬ A)) ⇒ ¬ A
brower f = f ∘ contradiction

data K (A : Prop) : Prop where
  Known : A ⇒ K A

postulate consist : ¬ (K ⊥)

distr : {A B : Prop} → K (A ⇒ B) ⇒ K A ⇒ K B
distr (Known f) (Known x) = (Known (f x))

andK : {A B : Prop} → K (A ∧ B) ⇒ (K A ∧ K B)
andK (Known (a , b)) = (Known (elim∧₁ (a , b)), Known (elim∧₂ (a , b)))

hold₁ : {A : Prop} → K A ⇒ K (K A)
hold₁ (Known x) = Known (Known x)

hold₂ : {A : Prop} → ¬(K A) ⇒ K (¬ (K A))
hold₂ x = Known x

IELTheorem₁ : {A : Prop} → K A ⇒ ¬ (¬ A)
IELTheorem₁ (Known x) = double x

IELTheorem₂ : {A : Prop} → ¬ A ⇒ ¬ (K A)
IELTheorem₂ f (Known x) = f x

spike : {A : Prop} → K A ⇒ A
spike (Known x) = x
IELTheorem₃ : {A : Prop} → ¬ (¬ (K A ⇒ A))
IELTheorem₃ f = f spike

IELTheorem₄ : {A : Prop} → ¬ (K A ∧ ¬ A)
IELTheorem₄ (Known x , x₁) = x₁ x
