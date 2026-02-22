-- definition 2.2.3
id : {A : Set} → A → A
id x = x

-- the "type ascription" operator
infixl 1 types
types : (A : Set) → A → A
types A x = x
syntax types A x  = x typed A

-- exercise 2.3
const : {A B : Set} → (b : B) → (a : A) → B
const b a = b

-- exercise 2.4
swap : {A B : Set} → {C : (a : A) → (b : B) → Set} →
       ((a : A) → (b : B) → C a b) →
       ((b : B) → (a : A) → C a b)
swap f b a = f a b

-- definition 2.2.5
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)
infixl 30 _∘_
