module _ where
  id : {A : Set} → A → A
  id x = x

  const : {A B : Set} → (b : B) → (a : A) → B
  const b a = b

  swap : {A B : Set} → {C : (a : A) → (b : B) → Set} →
          ((a : A) → (b : B) → C a b) →
          ((b : B) → (a : A) → C a b)
  swap f b a = f a b

  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
  f ∘ g = λ x → f (g x)
  infixl 30 _∘_
