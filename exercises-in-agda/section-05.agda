module _ where
  open import section-04 public

  -- definition 5.1.1, made universe-polymorphic for ContractionTo in section 10
  open import Agda.Primitive
  data _≡_ {i : Level} {A : Set i} (a : A) : A → Set i where
    refl : a ≡ a

  refl-at : {A : Set} → (a : A) → a ≡ a
  refl-at a = refl

  infix 5 _≡_

  ind-≡ : {A : Set} → {a : A} →
          (P : (x : A) → (a ≡ x) → Set) →
          P a refl →
          ((x : A) → (p : a ≡ x) → P x p)
  ind-≡ P parefl x refl = parefl

  module ≡-Basic where
    -- definition 5.2.1
    concat : {A : Set} → {x y z : A} →
             (x ≡ y) → (y ≡ z) → (x ≡ z)
    concat refl yz = yz

    _·_ : {A : Set} → {x y z : A} →
          (x ≡ y) → (y ≡ z) → (x ≡ z)
    _·_ = concat

    infixl 40 _·_

    -- definition 5.2.2
    inverse : {A : Set} → {x y : A} →
              (x ≡ y) → (y ≡ x)
    inverse refl = refl

    _⁻¹ : {A : Set} → {x y : A} →
          (p : x ≡ y) → y ≡ x
    _⁻¹ = inverse

    infix 54 _⁻¹

    module _ where
      open EmptyBasic
      _≢_ : {A : Set} → A → A → Set
      x ≢ y = ¬ (x ≡ y)

      ≢-inverse : {A : Set} → {x y : A} →
                  (x ≢ y) → (y ≢ x)
      ≢-inverse x≢y y≡x = x≢y (inverse y≡x)

    -- definition 5.2.3
    ·-assoc : {A : Set} → {x y z w : A} →
              (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
              p · q · r ≡ p · (q · r)
    ·-assoc refl p r = refl

    ·-unassoc : {A : Set} → {x y z w : A} →
                (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) →
                p · (q · r) ≡ p · q · r
    ·-unassoc p q r = inverse (·-assoc p q r)

    -- definition 5.2.4
    ·-lunit : {A : Set} → {x y : A} →
              (p : x ≡ y) → refl · p ≡ p
    ·-lunit p = refl

    ·-runit : {A : Set} → {x y : A} →
              (p : x ≡ y) → p · refl ≡ p
    ·-runit refl = refl

    -- definition 5.2.5
    ·-linv : {A : Set} → {x y : A} →
             (p : x ≡ y) → p ⁻¹ · p ≡ refl
    ·-linv refl = refl

    ·-rinv : {A : Set} → {x y : A} →
             (p : x ≡ y) → p · p ⁻¹ ≡ refl
    ·-rinv refl = refl

    -- definition 5.3.1
    ap : {A B : Set} → (f : A → B) → {x y : A} → (p : x ≡ y) → f x ≡ f y
    ap f refl = refl

    ap2 : {A B C : Set} →
          (f : A → B → C) → {x₁ x₂ : A} → (p : x₁ ≡ x₂) →
          {y₁ y₂ : B} → (q : y₁ ≡ y₂) →
          f x₁ y₁ ≡ f x₂ y₂
    ap2 f refl refl = refl

    ap3 : {A B C D : Set} →
          (f : A → B → C → D) → {x₁ x₂ : A} → (p : x₁ ≡ x₂) →
          {y₁ y₂ : B} → (q : y₁ ≡ y₂) →
          {z₁ z₂ : C} → (r : z₁ ≡ z₂) →
          f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
    ap3 f refl refl refl = refl

    ap4 : {A B C D E : Set} →
          (f : A → B → C → D → E) → {x₁ x₂ : A} → (p : x₁ ≡ x₂) →
          {y₁ y₂ : B} → (q : y₁ ≡ y₂) →
          {z₁ z₂ : C} → (r : z₁ ≡ z₂) →
          {w₁ w₂ : D} → (s : w₁ ≡ w₂) →
          f x₁ y₁ z₁ w₁ ≡ f x₂ y₂ z₂ w₂
    ap4 f refl refl refl refl = refl

    ap8 : {A1 A2 A3 A4 A5 A6 A7 A8 B : Set} →
          (f : A1 → A2 → A3 → A4 → A5 → A6 → A7 → A8 → B) →
          {x₁ x₂ : A1} → (p : x₁ ≡ x₂) →
          {y₁ y₂ : A2} → (q : y₁ ≡ y₂) →
          {z₁ z₂ : A3} → (r : z₁ ≡ z₂) →
          {w₁ w₂ : A4} → (s : w₁ ≡ w₂) →
          {v₁ v₂ : A5} → (t : v₁ ≡ v₂) →
          {u₁ u₂ : A6} → (u : u₁ ≡ u₂) →
          {a₁ a₂ : A7} → (v : a₁ ≡ a₂) →
          {b₁ b₂ : A8} → (w : b₁ ≡ b₂) →
          f x₁ y₁ z₁ w₁ v₁ u₁ a₁ b₁ ≡ f x₂ y₂ z₂ w₂ v₂ u₂ a₂ b₂
    ap8 f refl refl refl refl refl refl refl refl = refl

    ap-id : {A : Set} → {x y : A} →
            (p : x ≡ y) → ap id p ≡ p
    ap-id refl = refl

    ap-comp : {A B C : Set} → (g : B → C) → (f : A → B) →
              {x y : A} → (p : x ≡ y) →
              ap (g ∘ f) p ≡ ap g (ap f p)
    ap-comp g f refl = refl

    -- definition 5.3.2
    ap-refl : {A B : Set} → (f : A → B) → (x : A) → ap f {x} refl ≡ refl
    ap-refl f x = refl

    ap-inv : {A B : Set} → (f : A → B) → {x y : A} →
             (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
    ap-inv f refl = refl

    ap-concat : {A B : Set} → (f : A → B) → {x y z : A} →
                (p : x ≡ y) → (q : y ≡ z) →
                ap f (p · q) ≡ ap f p · ap f q
    ap-concat f refl q = refl

    -- definition 5.4.1
    tr : {A : Set} → (B : A → Set) →
         {x y : A} → (p : x ≡ y) →
         B x → B y
    tr B refl b = b

    tr2 : {A1 A2 : Set} → (B : A1 → A2 → Set) →
          {x₁ x₂ : A1} → (p : x₁ ≡ x₂) →
          {y₁ y₂ : A2} → (q : y₁ ≡ y₂) →
          B x₁ y₁ → B x₂ y₂
    tr2 B refl refl b = b

    tr3 : {A1 A2 A3 : Set} → (B : A1 → A2 → A3 → Set) →
          {x₁ x₂ : A1} → (p : x₁ ≡ x₂) →
          {y₁ y₂ : A2} → (q : y₁ ≡ y₂) →
          {z₁ z₂ : A3} → (r : z₁ ≡ z₂) →
          B x₁ y₁ z₁ → B x₂ y₂ z₂
    tr3 B refl refl refl b = b

    tr-concat : {A : Set} → {B : A → Set} → {x y z : A} →
                (p : x ≡ y) → (q : y ≡ z) → (b : B x) →
                tr B (p · q) b ≡ tr B q (tr B p b)
    tr-concat refl refl b = refl

    -- definition 5.4.2
    apd : {A : Set} → {B : A → Set} →
          (f : (a : A) → B a) →
          {x y : A} →
          (p : x ≡ y) →
          tr B p (f x) ≡ f y
    apd f refl = refl

    eq-then-pr₁-eq : {A : Set} → {B : A → Set} → {p1 p2 : Σ A B} → (p1 ≡ p2) → (Σ-Basic.pr₁ p1 ≡ Σ-Basic.pr₁ p2)
    eq-then-pr₁-eq refl = refl

    eq-×-then-pr₂-eq : {A : Set} → {B : Set} → {p1 p2 : A × B} → (p1 ≡ p2) → (Σ-Basic.pr₂ p1 ≡ Σ-Basic.pr₂ p2)
    eq-×-then-pr₂-eq refl = refl

  -- adapted from https://plfa.github.io/Equality/
  module ≡-Reasoning {A : Set} where
    open ≡-Basic public

    infix  1 begin_
    infixr 2 step-≡-∣ step-≡-⟩ step-≡-⟩⁻¹
    infix  3 _∎

    begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
    begin x≡y = x≡y

    step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
    step-≡-∣ x x≡y = x≡y

    step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
    step-≡-⟩ x y≡z x≡y = concat x≡y y≡z

    step-≡-⟩⁻¹ : ∀ (x : A) {y z : A} → y ≡ z → y ≡ x → x ≡ z
    step-≡-⟩⁻¹ x y≡z y≡x = concat (inverse y≡x) y≡z

    syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
    syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨ x≡y ⟩ y≡z
    syntax step-≡-⟩⁻¹ x y≡z y≡x =  x ≡⟨← y≡x ⟩ y≡z

    _∎ : ∀ (x : A) → x ≡ x
    x ∎  =  refl

  module ≡-Basic1 where
    open ≡-Reasoning

    -- proposition 5.5.1
    refl-uniq : {A : Set} → (a : A) → (y : Σ A (λ x → a ≡ x)) →
                (a , refl) ≡ y
    refl-uniq a (x , refl) = refl

    inv-inv : {A : Set} → {x y : A} → (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
    inv-inv refl = refl

    -- exercise 5.1
    distr-inv-concat : {A : Set} → {x y z : A} →
          (p : x ≡ y) → (q : y ≡ z) →
          (p · q) ⁻¹ ≡ q ⁻¹ · p ⁻¹
    distr-inv-concat refl q =
      begin
        (refl · q) ⁻¹
      ≡⟨⟩
        q ⁻¹
      ≡⟨← (·-runit (q ⁻¹)) ⟩
        q ⁻¹ · refl
      ≡⟨⟩
        q ⁻¹ · refl ⁻¹
      ∎

    -- exercise 5.2
    inv-con : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) →
              (p · q ≡ r) → (q ≡ p ⁻¹ · r)
    inv-con refl q r pqr = pqr

    inv-con-eq-refl : {A : Set} → {x y : A} → {p q : x ≡ y} →
                      (p ≡ q) → (q ⁻¹ · p ≡ refl)
    inv-con-eq-refl {A} {x} {y} {p} {q} refl = ·-linv q

    con-inv : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) →
              (p · q ≡ r) → (p ≡ r · q ⁻¹)
    con-inv p refl r pq≡r =
      begin
        p
      ≡⟨← (·-runit p) ⟩
        p · refl
      ≡⟨ pq≡r ⟩
        r
      ≡⟨← (·-runit r) ⟩
        r · refl
      ≡⟨⟩
        r · refl ⁻¹
      ∎

    con-cancel-right : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) →
                       (p ≡ r · q ⁻¹) → (p · q ≡ r)
    con-cancel-right refl refl r eq = eq · (·-runit r)

    -- exercise 5.3
    lift : {A : Set} → {B : A → Set} → {a x : A} →
          (p : a ≡ x) → (b : B a) → (a , b) ≡ (x , (tr B p b))
    lift refl b = refl

    -- exercise 5.4
    module exercise-5-4 where
      variable
        A : Set
        a b c d e : A
        p : a ≡ b
        q : b ≡ c
        r : c ≡ d
        s : d ≡ e

      -- exercise 5.4.a
      α₁ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           ((p · q) · r) · s ≡ (p · (q · r)) · s
      α₁ p q r s = ap (λ x → x · s) (·-assoc p q r)

      α₂ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           (p · (q · r)) · s ≡ p · ((q · r) · s)
      α₂ p q r s = ·-assoc p (q · r) s

      α₃ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           p · ((q · r) · s) ≡ p · (q · (r · s))
      α₃ p q r s = ap (λ x → p · x) (·-assoc q r s)

      α₄ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           ((p · q) · r) · s ≡ (p · q) · (r · s)
      α₄ p q r s = ·-assoc (p · q) r s

      α₅ : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
           (p · q) · (r · s) ≡ p · (q · (r · s))
      α₅ p q r s = ·-assoc p q (r · s)

      -- exercise 5.4.b
      pentagon : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
                 (α₁ p q r s) · (α₂ p q r s) · (α₃ p q r s) ≡ (α₄ p q r s) · (α₅ p q r s)
      pentagon refl refl refl refl = refl

  module UnitEquality where
    any-units-eq : (u v : Unit) → u ≡ v
    any-units-eq unit unit = refl

  module NatEquality where
    open NatBasic public
    open NatBasic.Symbolic
    open ≡-Reasoning

    predOrZero-succ : (n : Nat) → predOrZero (succ n) ≡ n
    predOrZero-succ n = refl

    -- proposition 5.6.1
    add-lunit : (n : Nat) → zero + n ≡ n
    add-lunit zero = refl
    add-lunit (succ n) =
      begin
        zero + (succ n)
      ≡⟨⟩
        succ (zero + n)
      ≡⟨ ap succ (add-lunit _) ⟩
        succ n
      ∎

    add-runit : (n : Nat) → (add n zero) ≡ n
    add-runit n = refl

    -- proposition 5.6.2
    add-succ-left : (m n : Nat) →
          (succ m) + n ≡ succ (m + n)
    add-succ-left m zero = refl
    add-succ-left m (succ n) =
      begin
        succ m + succ n
      ≡⟨⟩
        succ ((succ m) + n)
      ≡⟨ ap succ (add-succ-left _ _) ⟩
        succ (succ (m + n))
      ∎

    add-succ-right : (m n : Nat) → m + (succ n) ≡ succ (m + n)
    add-succ-right m n = refl

    -- proposition 5.6.3
    add-assoc : (m n k : Nat) → (m + n) + k ≡ m + (n + k)
    add-assoc m n zero = refl
    add-assoc m n (succ k) =
      begin
        (m + n) + (succ k)
      ≡⟨⟩
        succ ((m + n) + k)
      ≡⟨ ap succ (add-assoc m n k) ⟩
        succ (m + (n + k))
      ≡⟨⟩
        m + (n + (succ k))
      ∎

    add-unassoc : (m n k : Nat) → m + (n + k) ≡ (m + n) + k
    add-unassoc m n k = inverse (add-assoc m n k)

    -- proposition 5.6.4
    add-comm : (m n : Nat) → m + n ≡ n + m
    add-comm zero n = add-lunit n
    add-comm (succ m) n =
      begin
        (succ m) + n
      ≡⟨ add-succ-left _ _ ⟩
        succ (m + n)
      ≡⟨ ap succ (add-comm m n) ⟩
        succ (n + m)
      ≡⟨⟩
        n + (succ m)
      ∎

    add-add-rcomm : (m n k : Nat) → m + n + k ≡ m + k + n
    add-add-rcomm m n k =
      begin
        m + n + k
      ≡⟨ add-assoc m n k ⟩
        m + (n + k)
      ≡⟨ ap (λ e → m + e) (add-comm n k) ⟩
        m + (k + n)
      ≡⟨ add-unassoc m k n ⟩
        m + k + n
      ∎

  -- exercise 5.5
  module NatCommSemiring where
    open NatEquality public
    open NatBasic.Symbolic
    open ≡-Reasoning

    mul-rzero : (n : Nat) → n * zero ≡ zero
    mul-rzero n = refl

    mul-lzero : (n : Nat) → zero * n ≡ zero
    mul-lzero zero = refl
    mul-lzero (succ n) =
      begin
        zero * (succ n)
      ≡⟨⟩
        zero + (zero * n)
      ≡⟨ add-lunit _ ⟩
        zero * n
      ≡⟨ mul-lzero n ⟩
        zero
      ∎

    mul-runit : (n : Nat) → n * one ≡ n
    mul-runit n = refl

    mul-lunit : (n : Nat) → one * n ≡ n
    mul-lunit zero = refl
    mul-lunit (succ n) =
      begin
        one * (succ n)
      ≡⟨⟩
        one + (one * n)
      ≡⟨ ap (λ e → one + e) (mul-lunit _) ⟩
        one + n
      ≡⟨ add-comm one n ⟩
        n + one
      ≡⟨⟩
        succ n
      ∎

    mul-succ-right : (m n : Nat) → m * (succ n) ≡ m + m * n
    mul-succ-right m n = refl

    mul-succ-left : (m n : Nat) → (succ m) * n ≡ (m * n) + n
    mul-succ-left m zero =
      begin
        (succ m) * zero
      ≡⟨⟩
        zero
      ≡⟨ add-runit _ ⟩
        zero + zero
      ≡⟨⟩
        (m * zero) + zero
      ∎
    mul-succ-left m (succ n) =
      begin
        (succ m) * (succ n)
      ≡⟨⟩
        (succ m) + ((succ m) * n)
      ≡⟨ ap (λ e → (succ m) + e) (mul-succ-left m n) ⟩
        (succ m) + ((m * n) + n)
      ≡⟨ add-unassoc (succ m) (m * n) n ⟩
        ((succ m) + (m * n)) + n
      ≡⟨ ap (λ e → e + n) (add-succ-left _ _) ⟩
        succ (m + (m * n)) + n
      ≡⟨ add-succ-left _ _ ⟩
        succ ((m + (m * n)) + n)
      ≡⟨⟩
        (m * (succ n)) + (succ n)
      ∎

    -- exercise 5.5.b
    mul-comm : (m n : Nat) → m * n ≡ n * m
    mul-comm m zero =
      begin
        m * zero
      ≡⟨⟩
        zero
      ≡⟨← (mul-lzero m) ⟩
        zero * m
      ∎
    mul-comm m (succ n) =
      begin
        m * (succ n)
      ≡⟨ mul-succ-right m n ⟩
        m + (m * n)
      ≡⟨ ap (λ e → m + e) (mul-comm m n) ⟩
        m + (n * m)
      ≡⟨ add-comm m (n * m) ⟩
        (n * m) + m
      ≡⟨← (mul-succ-left n m) ⟩
        (succ n) * m
      ∎

    -- exercise 5.5.c
    mul-ldistr : (m n k : Nat) → m * (n + k) ≡ (m * n) + (m * k)
    mul-ldistr m n zero =
      begin
        m * (n + zero)
      ≡⟨⟩
        m * n
      ≡⟨ add-runit _ ⟩
        (m * n) + zero
      ≡⟨⟩
        (m * n) + (m * zero)
      ∎
    mul-ldistr m n (succ k) =
      begin
        m * (n + (succ k))
      ≡⟨⟩
        m * (succ (n + k))
      ≡⟨⟩
        m + (m * (n + k))
      ≡⟨ ap (λ e → m + e) (mul-ldistr m n k) ⟩
        m + ((m * n) + (m * k))
      ≡⟨ add-unassoc m (m * n) (m * k) ⟩
        (m + (m * n)) + (m * k)
      ≡⟨ ap (λ e → e + (m * k)) (add-comm m (m * n)) ⟩
        ((m * n) + m) + (m * k)
      ≡⟨ add-assoc (m * n) m (m * k) ⟩
        (m * n) + (m + (m * k))
      ≡⟨⟩
        (m * n) + (m * (succ k))
      ∎

    mul-rdistr : (m n k : Nat) → (m + n) * k ≡ (m * k) + (n * k)
    mul-rdistr m n k =
      begin
        (m + n) * k
      ≡⟨ mul-comm (m + n) k ⟩
        k * (m + n)
      ≡⟨ mul-ldistr k m n ⟩
        (k * m) + (k * n)
      ≡⟨ ap (λ e → e + (k * n)) (mul-comm k m) ⟩
        (m * k) + (k * n)
      ≡⟨ ap (λ e → (m * k) + e) (mul-comm k n) ⟩
        (m * k) + (n * k)
      ∎

    -- exercise 5.5.d
    mul-assoc : (m n k : Nat) → (m * n) * k ≡ m * (n * k)
    mul-assoc m n zero =
      begin
        (m * n) * zero
      ≡⟨⟩
        zero
      ≡⟨⟩
        m * zero
      ≡⟨⟩
        m * (n * zero)
      ∎
    mul-assoc m n (succ k) =
      begin
        (m * n) * (succ k)
      ≡⟨⟩
        (m * n) + ((m * n) * k)
      ≡⟨ ap (λ e → (m * n) + e) (mul-assoc m n k) ⟩
        (m * n) + (m * (n * k))
      ≡⟨← (mul-ldistr m n (n * k)) ⟩
        m * (n + n * k)
      ≡⟨⟩
        m * (n * (succ k))
      ∎

    mul-unassoc : (m n k : Nat) → m * (n * k) ≡ m * n * k
    mul-unassoc m n k = inverse (mul-assoc m n k)

  module IntEquality where
    open IntBasic public
    open ≡-Reasoning

    -- exercise 5.6
    Int-succ-pred : (x : Int) → Int-succ (pred x) ≡ x
    Int-succ-pred zeroInt = refl
    Int-succ-pred (posSucc zero) = refl
    Int-succ-pred (posSucc (succ n)) = refl
    Int-succ-pred (negSucc n) = refl

    Int-pred-succ : (x : Int) → pred (Int-succ x) ≡ x
    Int-pred-succ zeroInt = refl
    Int-pred-succ (posSucc n) = refl
    Int-pred-succ (negSucc zero) = refl
    Int-pred-succ (negSucc (succ n)) = refl

    -- exercise 5.7
    module IntAddAbGroup where
      open IntBasic public
      open NatBasic.SymbolicQualified
      open IntBasic.Symbolic
      open IntBasic.SymbolicQualified
      open ≡-Reasoning

      -- exercise 5.7.a
      add-lunit : (x : Int) → zeroInt + x ≡ x
      add-lunit zeroInt = refl
      add-lunit (posSucc n) =
        begin
          zeroInt + (posSucc n)
        ≡⟨⟩
          (zero +ℕ (succ n)) -ℕ (zero +ℕ zero)
        ≡⟨⟩
          (zero +ℕ (succ n)) -ℕ zero
        ≡⟨ ap (λ e → e -ℕ zero) (NatEquality.add-lunit (succ n)) ⟩
          (succ n) -ℕ zero
        ≡⟨⟩
          posSucc n
        ∎
      add-lunit (negSucc n) =
        begin
          zeroInt + (negSucc n)
        ≡⟨⟩
          (zero +ℕ zero) -ℕ (zero +ℕ (succ n))
        ≡⟨⟩
          zero -ℕ (zero +ℕ (succ n))
        ≡⟨ ap (λ e → zero -ℕ e) (NatEquality.add-lunit (succ n)) ⟩
          zero -ℕ (succ n)
        ≡⟨⟩
          negSucc n
        ∎

      add-runit : (x : Int) → x + zeroInt ≡ x
      add-runit zeroInt = refl
      add-runit (posSucc n) = refl
      add-runit (negSucc n) = refl

      Nat-minus-asNatDiff : (x : Int) → (let (x₊ , x₋) = asNatDiff x in x₊ -ℕ x₋) ≡ x
      Nat-minus-asNatDiff zeroInt = refl
      Nat-minus-asNatDiff (posSucc zero) = refl
      Nat-minus-asNatDiff (posSucc (succ n)) = refl
      Nat-minus-asNatDiff (negSucc zero) = refl
      Nat-minus-asNatDiff (negSucc (succ n)) = refl

      pred-Nat-minus : (n m : Nat) → pred (n -ℕ m) ≡ n -ℕ (succ m)
      pred-Nat-minus zero zero = refl
      pred-Nat-minus zero (succ m) = refl
      pred-Nat-minus (succ zero) zero = refl
      pred-Nat-minus (succ zero) (succ m) =
        begin
          pred ((succ zero) -ℕ (succ m))
        ≡⟨⟩
          pred (zero -ℕ m)
        ≡⟨ pred-Nat-minus zero m ⟩
          zero -ℕ (succ m)
        ≡⟨⟩
          (succ zero) -ℕ (succ (succ m))
        ∎
      pred-Nat-minus (succ (succ n)) zero = refl
      pred-Nat-minus (succ (succ n)) (succ m) =
        begin
          pred ((succ (succ n)) -ℕ (succ m))
        ≡⟨⟩
          pred ((succ n) -ℕ m)
        ≡⟨ pred-Nat-minus (succ n) m ⟩
          (succ n) -ℕ (succ m)
        ≡⟨⟩
          (succ (succ n)) -ℕ (succ (succ m))
        ∎

      succ-Nat-minus : (n m : Nat) → Int-succ (n -ℕ m) ≡ (succ n) -ℕ m
      succ-Nat-minus zero zero = refl
      succ-Nat-minus (succ n) zero = refl
      succ-Nat-minus zero (succ zero) = refl
      succ-Nat-minus (succ n) (succ zero) =
        begin
          Int-succ ((succ n) -ℕ (succ zero))
        ≡⟨⟩
          Int-succ (n -ℕ zero)
        ≡⟨ succ-Nat-minus n zero ⟩
          (succ n) -ℕ zero
        ≡⟨⟩
          (succ (succ n)) -ℕ (succ zero)
        ∎
      succ-Nat-minus zero (succ (succ m)) = refl
      succ-Nat-minus (succ n) (succ (succ m)) =
        begin
          Int-succ ((succ n) -ℕ (succ (succ m)))
        ≡⟨⟩
          Int-succ (n -ℕ (succ m))
        ≡⟨ succ-Nat-minus n (succ m) ⟩
          (succ n) -ℕ (succ m)
        ≡⟨⟩
          (succ (succ n)) -ℕ (succ (succ m))
        ∎

      asNatDiff-Nat-minus-normalization :
            (x₊ x₋ : Nat) → (
              let (x₊' , x₋') = asNatDiff (x₊ -ℕ x₋)
              in Σ Nat (λ k → (x₊ ≡ x₊' +ℕ k) × (x₋ ≡ x₋' +ℕ k)))
      asNatDiff-Nat-minus-normalization zero zero = (zero , refl , refl)
      asNatDiff-Nat-minus-normalization (succ x₊) zero = (zero , refl , refl)
      asNatDiff-Nat-minus-normalization zero (succ x₋) = (zero , refl , refl)
      asNatDiff-Nat-minus-normalization (succ x₊) (succ x₋) =
        let (k , nx₊ , nx₋) = asNatDiff-Nat-minus-normalization x₊ x₋
        in (succ k , ap succ nx₊ , ap succ nx₋)

      Nat-minus-add-same :
            (x y k : Nat) →
            (x +ℕ k) -ℕ (y +ℕ k) ≡ x -ℕ y
      Nat-minus-add-same x y zero = refl
      Nat-minus-add-same x y (succ k) =
        begin
          (x +ℕ (succ k)) -ℕ (y +ℕ (succ k))
        ≡⟨⟩
          (succ (x +ℕ k)) -ℕ (succ (y +ℕ k))
        ≡⟨⟩
          (x +ℕ k) -ℕ (y +ℕ k)
        ≡⟨ Nat-minus-add-same x y k ⟩
          x -ℕ y
        ∎

      Nat-minus-add : (x₊ x₋ y₊ y₋ : Nat) →
            (x₊ -ℕ x₋) + (y₊ -ℕ y₋) ≡ (x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋)
      Nat-minus-add x₊ x₋ y₊ y₋ =
        let (x₊' , x₋') = asNatDiff (x₊ -ℕ x₋)
            (y₊' , y₋') = asNatDiff (y₊ -ℕ y₋)
            (kx , nx₊ , nx₋) = asNatDiff-Nat-minus-normalization x₊ x₋
            (ky , ny₊ , ny₋) = asNatDiff-Nat-minus-normalization y₊ y₋
        in
          begin
            (x₊ -ℕ x₋) + (y₊ -ℕ y₋)
          ≡⟨⟩
            (x₊' +ℕ y₊') -ℕ (x₋' +ℕ y₋')
          ≡⟨← (Nat-minus-add-same (x₊' +ℕ y₊') (x₋' +ℕ y₋') kx) ⟩
            ((x₊' +ℕ y₊') +ℕ kx) -ℕ
            ((x₋' +ℕ y₋') +ℕ kx)
          ≡⟨← (Nat-minus-add-same ((x₊' +ℕ y₊') +ℕ kx) ((x₋' +ℕ y₋') +ℕ kx) ky) ⟩
            (((x₊' +ℕ y₊') +ℕ kx) +ℕ ky) -ℕ
            (((x₋' +ℕ y₋') +ℕ kx) +ℕ ky)
          ≡⟨ (
            let
              rearrange : (a b c d : Nat) →
                    (((a +ℕ b) +ℕ c) +ℕ d) ≡
                    (a +ℕ c) +ℕ (b +ℕ d)
              rearrange a b c d =
                begin
                  ((a +ℕ b) +ℕ c) +ℕ d
                ≡⟨ ap (λ e → e +ℕ d) (NatEquality.add-assoc a b c) ⟩
                  (a +ℕ (b +ℕ c)) +ℕ d
                ≡⟨ ap (λ e → (a +ℕ e) +ℕ d) (NatEquality.add-comm b c) ⟩
                  (a +ℕ (c +ℕ b)) +ℕ d
                ≡⟨ ap (λ e → e +ℕ d) (NatEquality.add-unassoc a c b)⟩
                  ((a +ℕ c) +ℕ b) +ℕ d
                ≡⟨ NatEquality.add-assoc _ b d ⟩
                  (a +ℕ c) +ℕ (b +ℕ d)
                ∎
            in
              ap2 (λ e1 e2 → e1 -ℕ e2) (rearrange x₊' y₊' kx ky) (rearrange x₋' y₋' kx ky)
          ) ⟩
            ((x₊' +ℕ kx) +ℕ (y₊' +ℕ ky)) -ℕ
            ((x₋' +ℕ kx) +ℕ (y₋' +ℕ ky))
          ≡⟨← (
            ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4)) nx₊ ny₊ nx₋ ny₋
          ) ⟩
            (x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋)
          ∎

      -- exercise 5.7.b
      add-pred-left : (x y : Int) → pred x + y ≡ pred (x + y)
      add-pred-left x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            pred x + y
          ≡⟨ ap2 (λ e1 e2 → pred e1 + e2) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
            pred (x₊ -ℕ x₋) + (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → e + (y₊ -ℕ y₋)) (pred-Nat-minus x₊ x₋) ⟩
            (x₊ -ℕ (succ x₋)) + (y₊ -ℕ y₋)
          ≡⟨ Nat-minus-add x₊ (succ x₋) y₊ y₋ ⟩
            (x₊ +ℕ y₊) -ℕ ((succ x₋) +ℕ y₋)
          ≡⟨ ap (λ e → (x₊ +ℕ y₊) -ℕ e) (NatEquality.add-succ-left x₋ y₋) ⟩
            (x₊ +ℕ y₊) -ℕ (succ (x₋ +ℕ y₋))
          ≡⟨← (pred-Nat-minus (x₊ +ℕ y₊) (x₋ +ℕ y₋)) ⟩
            pred ((x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋))
          ≡⟨⟩
            pred (x + y)
          ∎

      add-pred-right : (x y : Int) → x + pred y ≡ pred (x + y)
      add-pred-right x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            x + pred y
          ≡⟨ ap2 (λ e1 e2 → e1 + pred e2) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
            (x₊ -ℕ x₋) + pred (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → (x₊ -ℕ x₋) + e) (pred-Nat-minus y₊ y₋) ⟩
            (x₊ -ℕ x₋) + (y₊ -ℕ (succ y₋))
          ≡⟨ Nat-minus-add x₊ x₋ y₊ (succ y₋) ⟩
            (x₊ +ℕ y₊) -ℕ (x₋ +ℕ (succ y₋))
          ≡⟨⟩
            (x₊ +ℕ y₊) -ℕ (succ (x₋ +ℕ y₋))
          ≡⟨← (pred-Nat-minus (x₊ +ℕ y₊) (x₋ +ℕ y₋)) ⟩
            pred ((x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋))
          ≡⟨⟩
            pred (x + y)
          ∎

      add-succ-left : (x y : Int) → Int-succ x + y ≡ Int-succ (x + y)
      add-succ-left x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            Int-succ x + y
          ≡⟨ ap2 (λ e1 e2 → Int-succ e1 + e2) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
            Int-succ (x₊ -ℕ x₋) + (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → e + (y₊ -ℕ y₋)) (succ-Nat-minus x₊ x₋) ⟩
            ((succ x₊) -ℕ x₋) + (y₊ -ℕ y₋)
          ≡⟨ Nat-minus-add (succ x₊) x₋ y₊ y₋ ⟩
            ((succ x₊) +ℕ y₊) -ℕ (x₋ +ℕ y₋)
          ≡⟨ ap (λ e → e -ℕ (x₋ +ℕ y₋)) (NatEquality.add-succ-left x₊ y₊) ⟩
            (succ (x₊ +ℕ y₊)) -ℕ (x₋ +ℕ y₋)
          ≡⟨← (succ-Nat-minus (x₊ +ℕ y₊) (x₋ +ℕ y₋)) ⟩
            Int-succ ((x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋))
          ≡⟨⟩
            Int-succ (x + y)
          ∎

      add-succ-right : (x y : Int) → x + Int-succ y ≡ Int-succ (x + y)
      add-succ-right x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            x + Int-succ y
          ≡⟨ ap2 (λ e1 e2 → e1 + Int-succ e2) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
            (x₊ -ℕ x₋) + Int-succ (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → (x₊ -ℕ x₋) + e) (succ-Nat-minus y₊ y₋) ⟩
            (x₊ -ℕ x₋) + ((succ y₊) -ℕ y₋)
          ≡⟨ Nat-minus-add x₊ x₋ (succ y₊) y₋ ⟩
            (x₊ +ℕ (succ y₊)) -ℕ (x₋ +ℕ y₋)
          ≡⟨⟩
            (succ (x₊ +ℕ y₊)) -ℕ (x₋ +ℕ y₋)
          ≡⟨← (succ-Nat-minus (x₊ +ℕ y₊) (x₋ +ℕ y₋)) ⟩
            Int-succ ((x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋))
          ≡⟨⟩
            Int-succ (x + y)
          ∎

      -- exercise 5.7.c
      add-assoc : (x y z : Int) → (x + y) + z ≡ x + (y + z)
      add-assoc x y z =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
          (z₊ , z₋) = asNatDiff z
        in
          begin
            (x + y) + z
          ≡⟨ ap (λ e → (x + y) + e) (inverse (Nat-minus-asNatDiff z)) ⟩
            (x + y) + (z₊ -ℕ z₋)
          ≡⟨⟩
            ((x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋)) + (z₊ -ℕ z₋)
          ≡⟨ Nat-minus-add (x₊ +ℕ y₊) (x₋ +ℕ y₋) z₊ z₋ ⟩
            ((x₊ +ℕ y₊) +ℕ z₊) -ℕ
            ((x₋ +ℕ y₋) +ℕ z₋)
          ≡⟨ ap2 (λ e1 e2 → e1 -ℕ e2) (NatEquality.add-assoc x₊ y₊ z₊) (NatEquality.add-assoc x₋ y₋ z₋) ⟩
            (x₊ +ℕ (y₊ +ℕ z₊)) -ℕ
            (x₋ +ℕ (y₋ +ℕ z₋))
          ≡⟨← (Nat-minus-add x₊ x₋ (y₊ +ℕ z₊) (y₋ +ℕ z₋)) ⟩
            (x₊ -ℕ x₋) + ((y₊ +ℕ z₊) -ℕ (y₋ +ℕ z₋))
          ≡⟨⟩
            (x₊ -ℕ x₋) + (y + z)
          ≡⟨ ap (λ e → e + (y + z)) (Nat-minus-asNatDiff x) ⟩
            x + (y + z)
          ∎

      add-comm : (x y : Int) → x + y ≡ y + x
      add-comm x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            x + y
          ≡⟨ ap2 (λ e1 e2 → e1 + e2) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
            (x₊ -ℕ x₋) + (y₊ -ℕ y₋)
          ≡⟨ Nat-minus-add x₊ x₋ y₊ y₋ ⟩
            (x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋)
          ≡⟨ ap2 (λ e1 e2 → e1 -ℕ e2) (NatEquality.add-comm x₊ y₊) (NatEquality.add-comm x₋ y₋) ⟩
            (y₊ +ℕ x₊) -ℕ (y₋ +ℕ x₋)
          ≡⟨← (Nat-minus-add y₊ y₋ x₊ x₋) ⟩
            (y₊ -ℕ y₋) + (x₊ -ℕ x₋)
          ≡⟨ ap2 (λ e1 e2 → e1 + e2) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff x) ⟩
            y + x
          ∎

      -- exercise 5.7.d
      Nat-minus-eq-zero : (x : Nat) → x -ℕ x ≡ zeroInt
      Nat-minus-eq-zero zero = refl
      Nat-minus-eq-zero (succ x) =
        begin
          (succ x) -ℕ (succ x)
        ≡⟨⟩
          x -ℕ x
        ≡⟨ Nat-minus-eq-zero x ⟩
          zeroInt
        ∎

      left-inverse : (x : Int) → (- x) + x ≡ zeroInt
      left-inverse zeroInt = refl
      left-inverse (posSucc n) =
        begin
          (- (posSucc n)) + (posSucc n)
        ≡⟨⟩
          (zero +ℕ n) -ℕ n
        ≡⟨ ap (λ e → e -ℕ n) (NatEquality.add-lunit n) ⟩
          n -ℕ n
        ≡⟨ Nat-minus-eq-zero n ⟩
          zeroInt
        ∎
      left-inverse (negSucc n) =
        begin
          (- (negSucc n)) + (negSucc n)
        ≡⟨⟩
          n -ℕ (zero +ℕ n)
        ≡⟨ ap (λ e → n -ℕ e) (NatEquality.add-lunit n) ⟩
          n -ℕ n
        ≡⟨ Nat-minus-eq-zero n ⟩
          zeroInt
        ∎

      right-inverse : (x : Int) → x + (- x) ≡ zeroInt
      right-inverse zeroInt = refl
      right-inverse (posSucc n) =
        begin
          (posSucc n) + (- (posSucc n))
        ≡⟨⟩
          n -ℕ (zero +ℕ n)
        ≡⟨ ap (λ e → n -ℕ e) (NatEquality.add-lunit n) ⟩
          n -ℕ n
        ≡⟨ Nat-minus-eq-zero n ⟩
          zeroInt
        ∎
      right-inverse (negSucc n) =
        begin
          (negSucc n) + (- (negSucc n))
        ≡⟨⟩
          (zero +ℕ n) -ℕ n
        ≡⟨ ap (λ e → e -ℕ n) (NatEquality.add-lunit n) ⟩
          n -ℕ n
        ≡⟨ Nat-minus-eq-zero n ⟩
          zeroInt
        ∎

    -- exercise 5.8
    module IntCommRing where
      open IntAddAbGroup public
      open NatBasic.SymbolicQualified
      open IntBasic.Symbolic
      open IntBasic.SymbolicQualified
      open ≡-Reasoning

      -- exercise 5.8.a
      mul-lzero : (x : Int) → zeroInt * x ≡ zeroInt
      mul-lzero x =
        let
          (x₊ , x₋) = asNatDiff x
        in
          begin
            zeroInt * x
          ≡⟨⟩
            ((zero *ℕ x₊) +ℕ (zero *ℕ x₋)) -ℕ
            ((zero *ℕ x₋) +ℕ (zero *ℕ x₊))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4))
              (NatCommSemiring.mul-lzero x₊)
              (NatCommSemiring.mul-lzero x₋)
              (NatCommSemiring.mul-lzero x₋)
              (NatCommSemiring.mul-lzero x₊)
          ⟩
            (zero +ℕ zero) -ℕ (zero +ℕ zero)
          ≡⟨⟩
            zeroInt
          ∎

      mul-rzero : (x : Int) → x * zeroInt ≡ zeroInt
      mul-rzero x = refl

      mul-lunit : (x : Int) → Int-one * x ≡ x
      mul-lunit x =
        let
          (x₊ , x₋) = asNatDiff x
        in
          begin
            Int-one * x
          ≡⟨⟩
            (((succ zero) *ℕ x₊) +ℕ (zero *ℕ x₋)) -ℕ
            (((succ zero) *ℕ x₋) +ℕ (zero *ℕ x₊))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4))
              (NatCommSemiring.mul-lunit x₊)
              (NatCommSemiring.mul-lzero x₋)
              (NatCommSemiring.mul-lunit x₋)
              (NatCommSemiring.mul-lzero x₊)
          ⟩
            (x₊ +ℕ zero) -ℕ (x₋ +ℕ zero)
          ≡⟨⟩
            x₊ -ℕ x₋
          ≡⟨ Nat-minus-asNatDiff x ⟩
            x
          ∎

      mul-runit : (x : Int) → x * Int-one ≡ x
      mul-runit x =
        let
          (x₊ , x₋) = asNatDiff x
        in
          begin
            x * Int-one
          ≡⟨⟩
            x₊ -ℕ (zero +ℕ x₋)
          ≡⟨ ap (λ e → x₊ -ℕ e) (NatEquality.add-lunit x₋) ⟩
            x₊ -ℕ x₋
          ≡⟨ Nat-minus-asNatDiff x ⟩
            x
          ∎

      Nat-minus-mul : (x₊ x₋ y₊ y₋ : Nat) →
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋) ≡ (
              ((x₊ *ℕ y₊) +ℕ (x₋ *ℕ y₋)) -ℕ
              ((x₊ *ℕ y₋) +ℕ (x₋ *ℕ y₊))
            )
      Nat-minus-mul x₊ x₋ y₊ y₋ =
        let (x₊' , x₋') = asNatDiff (x₊ -ℕ x₋)
            (y₊' , y₋') = asNatDiff (y₊ -ℕ y₋)
            (kx , nx₊ , nx₋) = asNatDiff-Nat-minus-normalization x₊ x₋
            (ky , ny₊ , ny₋) = asNatDiff-Nat-minus-normalization y₊ y₋

            expandCrossTerm : (a b c d : Nat) →
                  (a +ℕ b) *ℕ (c +ℕ d) ≡
                  (a *ℕ c) +ℕ (a *ℕ d) +ℕ (b *ℕ c) +ℕ (b *ℕ d)
            expandCrossTerm a b c d =
              begin
                (a +ℕ b) *ℕ (c +ℕ d)
              ≡⟨ NatCommSemiring.mul-ldistr (a +ℕ b) c d ⟩
                (a +ℕ b) *ℕ c +ℕ (a +ℕ b) *ℕ d
              ≡⟨ ap2 (λ e1 e2 → e1 +ℕ e2) (NatCommSemiring.mul-rdistr a b c) (NatCommSemiring.mul-rdistr a b d) ⟩
                (a *ℕ c +ℕ b *ℕ c) +ℕ (a *ℕ d +ℕ b *ℕ d)
              ≡⟨ (
                let
                  unassoc-lhs : (a *ℕ c +ℕ b *ℕ c) +ℕ (a *ℕ d +ℕ b *ℕ d) ≡ a *ℕ c +ℕ b *ℕ c +ℕ a *ℕ d +ℕ b *ℕ d
                  unassoc-lhs = NatCommSemiring.add-unassoc (a *ℕ c +ℕ b *ℕ c) (a *ℕ d) (b *ℕ d)
                  permute : a *ℕ c +ℕ b *ℕ c +ℕ a *ℕ d +ℕ b *ℕ d ≡ a *ℕ c +ℕ a *ℕ d +ℕ b *ℕ c +ℕ b *ℕ d
                  permute = ap (λ e → e +ℕ b *ℕ d) (NatCommSemiring.add-add-rcomm (a *ℕ c) (b *ℕ c) (a *ℕ d))
                in unassoc-lhs · permute
              ) ⟩
                (a *ℕ c) +ℕ (a *ℕ d) +ℕ (b *ℕ c) +ℕ (b *ℕ d)
              ∎

            rearrangeFirst : (t1 t2 t3 t4 t5 t6 t7 : Nat) →
                  t1 +ℕ t2 +ℕ (t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5) ≡
                  (t1 +ℕ t3 +ℕ t4 +ℕ t5) +ℕ (t2 +ℕ t6 +ℕ t7 +ℕ t5)
            rearrangeFirst t1 t2 t3 t4 t5 t6 t7 =
              let
                unassoc-lhs : t1 +ℕ t2 +ℕ (t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5) ≡ t1 +ℕ t2 +ℕ t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5
                unassoc-lhs =
                  NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7) t5
                  · ap (λ e → e +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4 +ℕ t5 +ℕ t6) t7)
                  · ap (λ e → e +ℕ t7 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4 +ℕ t5) t6)
                  · ap (λ e → e +ℕ t6 +ℕ t7 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4) t5)
                  · ap (λ e → e +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) t3 t4)

                permute : t1 +ℕ t2 +ℕ t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5 ≡ t1 +ℕ t3 +ℕ t4 +ℕ t5 +ℕ t2 +ℕ t6 +ℕ t7 +ℕ t5
                permute =
                  ap (λ e → e +ℕ t6 +ℕ t7 +ℕ t5) (
                    ap (λ e → e +ℕ t4 +ℕ t5) (NatCommSemiring.add-add-rcomm t1 t2 t3)
                    · ap (λ e → e +ℕ t5) (NatCommSemiring.add-add-rcomm (t1 +ℕ t3) t2 t4)
                    · NatCommSemiring.add-add-rcomm (t1 +ℕ t3 +ℕ t4) t2 t5
                  )

                unassoc-rhs : (t1 +ℕ t3 +ℕ t4 +ℕ t5) +ℕ (t2 +ℕ t6 +ℕ t7 +ℕ t5) ≡ t1 +ℕ t3 +ℕ t4 +ℕ t5 +ℕ t2 +ℕ t6 +ℕ t7 +ℕ t5
                unassoc-rhs =
                  NatCommSemiring.add-unassoc (t1 +ℕ t3 +ℕ t4 +ℕ t5) (t2 +ℕ t6 +ℕ t7) t5
                  · ap (λ e → e +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t3 +ℕ t4 +ℕ t5) (t2 +ℕ t6) t7)
                  · ap (λ e → e +ℕ t7 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t3 +ℕ t4 +ℕ t5) t2 t6)
              in unassoc-lhs · permute · (inverse unassoc-rhs)

            rearrangeSecond : (t1 t2 t3 t4 t5 t6 t7 : Nat) →
                  t1 +ℕ t2 +ℕ (t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5) ≡
                  (t1 +ℕ t3 +ℕ t7 +ℕ t5) +ℕ (t2 +ℕ t6 +ℕ t4 +ℕ t5)
            rearrangeSecond t1 t2 t3 t4 t5 t6 t7 =
              let
                unassoc-lhs : t1 +ℕ t2 +ℕ (t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5) ≡ t1 +ℕ t2 +ℕ t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5
                unassoc-lhs =
                  NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7) t5
                  · ap (λ e → e +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4 +ℕ t5 +ℕ t6) t7)
                  · ap (λ e → e +ℕ t7 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4 +ℕ t5) t6)
                  · ap (λ e → e +ℕ t6 +ℕ t7 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) (t3 +ℕ t4) t5)
                  · ap (λ e → e +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t2) t3 t4)

                permute : t1 +ℕ t2 +ℕ t3 +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7 +ℕ t5 ≡ t1 +ℕ t3 +ℕ t7 +ℕ t5 +ℕ t2 +ℕ t6 +ℕ t4 +ℕ t5
                permute =
                  ap (λ e → e +ℕ t5) ( -- fix t5
                    ap (λ e → e +ℕ t4 +ℕ t5 +ℕ t6 +ℕ t7) (NatCommSemiring.add-add-rcomm t1 t2 t3)     -- sink t3
                    · NatCommSemiring.add-add-rcomm (t1 +ℕ t3 +ℕ t2 +ℕ t4 +ℕ t5) t6 t7                -- sink t7
                    · ap (λ e → e +ℕ t6) (NatCommSemiring.add-add-rcomm (t1 +ℕ t3 +ℕ t2 +ℕ t4) t5 t7) -- sink t7
                    · ap (λ e → e +ℕ t5 +ℕ t6) (NatCommSemiring.add-add-rcomm (t1 +ℕ t3 +ℕ t2) t4 t7) -- sink t7
                    · ap (λ e → e +ℕ t4 +ℕ t5 +ℕ t6) (NatCommSemiring.add-add-rcomm (t1 +ℕ t3) t2 t7) -- sink t7
                    · ap (λ e → e +ℕ t6) (NatCommSemiring.add-add-rcomm (t1 +ℕ t3 +ℕ t7 +ℕ t2) t4 t5) -- sink t5
                    · ap (λ e → e +ℕ t4 +ℕ t6) (NatCommSemiring.add-add-rcomm (t1 +ℕ t3 +ℕ t7) t2 t5) -- sink t5
                    · NatCommSemiring.add-add-rcomm (t1 +ℕ t3 +ℕ t7 +ℕ t5 +ℕ t2) t4 t6                -- sink t6
                  )

                unassoc-rhs : (t1 +ℕ t3 +ℕ t7 +ℕ t5) +ℕ (t2 +ℕ t6 +ℕ t4 +ℕ t5) ≡ t1 +ℕ t3 +ℕ t7 +ℕ t5 +ℕ t2 +ℕ t6 +ℕ t4 +ℕ t5
                unassoc-rhs =
                  NatCommSemiring.add-unassoc (t1 +ℕ t3 +ℕ t7 +ℕ t5) (t2 +ℕ t6 +ℕ t4) t5
                  · ap (λ e → e +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t3 +ℕ t7 +ℕ t5) (t2 +ℕ t6) t4)
                  · ap (λ e → e +ℕ t4 +ℕ t5) (NatCommSemiring.add-unassoc (t1 +ℕ t3 +ℕ t7 +ℕ t5) t2 t6)
              in unassoc-lhs · permute · (inverse unassoc-rhs)

        in
          begin
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋)
          ≡⟨⟩
            ((x₊' *ℕ y₊') +ℕ (x₋' *ℕ y₋')) -ℕ
            ((x₊' *ℕ y₋') +ℕ (x₋' *ℕ y₊'))
          ≡⟨← (Nat-minus-add-same ((x₊' *ℕ y₊') +ℕ (x₋' *ℕ y₋')) ((x₊' *ℕ y₋') +ℕ (x₋' *ℕ y₊')) (x₊' *ℕ ky +ℕ kx *ℕ y₊' +ℕ kx *ℕ ky +ℕ x₋' *ℕ ky +ℕ kx *ℕ y₋' +ℕ kx *ℕ ky)) ⟩
            ((x₊' *ℕ y₊') +ℕ (x₋' *ℕ y₋') +ℕ (x₊' *ℕ ky +ℕ kx *ℕ y₊' +ℕ kx *ℕ ky +ℕ x₋' *ℕ ky +ℕ kx *ℕ y₋' +ℕ kx *ℕ ky)) -ℕ
            ((x₊' *ℕ y₋') +ℕ (x₋' *ℕ y₊') +ℕ (x₊' *ℕ ky +ℕ kx *ℕ y₊' +ℕ kx *ℕ ky +ℕ x₋' *ℕ ky +ℕ kx *ℕ y₋' +ℕ kx *ℕ ky))
          ≡⟨ ap2 (λ e1 e2 → e1 -ℕ e2)
              (rearrangeFirst (x₊' *ℕ y₊') (x₋' *ℕ y₋') (x₊' *ℕ ky) (kx *ℕ y₊') (kx *ℕ ky) (x₋' *ℕ ky) (kx *ℕ y₋'))
              (rearrangeSecond (x₊' *ℕ y₋') (x₋' *ℕ y₊') (x₊' *ℕ ky) (kx *ℕ y₊') (kx *ℕ ky) (x₋' *ℕ ky) (kx *ℕ y₋'))
          ⟩
            (((x₊' *ℕ y₊') +ℕ (x₊' *ℕ ky) +ℕ (kx *ℕ y₊') +ℕ (kx *ℕ ky)) +ℕ ((x₋' *ℕ y₋') +ℕ (x₋' *ℕ ky) +ℕ (kx *ℕ y₋') +ℕ (kx *ℕ ky))) -ℕ
            (((x₊' *ℕ y₋') +ℕ (x₊' *ℕ ky) +ℕ (kx *ℕ y₋') +ℕ (kx *ℕ ky)) +ℕ ((x₋' *ℕ y₊') +ℕ (x₋' *ℕ ky) +ℕ (kx *ℕ y₊') +ℕ (kx *ℕ ky)))
          ≡⟨← (ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4)) (expandCrossTerm x₊' kx y₊' ky) (expandCrossTerm x₋' kx y₋' ky) (expandCrossTerm x₊' kx y₋' ky) (expandCrossTerm x₋' kx y₊' ky)) ⟩
            (((x₊' +ℕ kx) *ℕ (y₊' +ℕ ky)) +ℕ ((x₋' +ℕ kx) *ℕ (y₋' +ℕ ky))) -ℕ
            (((x₊' +ℕ kx) *ℕ (y₋' +ℕ ky)) +ℕ ((x₋' +ℕ kx) *ℕ (y₊' +ℕ ky)))
          ≡⟨← (ap8 (λ e1 e2 e3 e4 e5 e6 e7 e8 → ((e1 *ℕ e2) +ℕ (e3 *ℕ e4)) -ℕ ((e5 *ℕ e6) +ℕ (e7 *ℕ e8))) nx₊ ny₊ nx₋ ny₋ nx₊ ny₋ nx₋ ny₊) ⟩
            ((x₊ *ℕ y₊) +ℕ (x₋ *ℕ y₋)) -ℕ ((x₊ *ℕ y₋) +ℕ (x₋ *ℕ y₊))
          ∎

      neg-Nat-minus : (x₊ x₋ : Nat) → (- (x₊ -ℕ x₋)) ≡ (x₋ -ℕ x₊)
      neg-Nat-minus x₊ x₋ =
        let
          (x₊' , x₋') = asNatDiff (x₊ -ℕ x₋)
          (kx , nx₊ , nx₋) = asNatDiff-Nat-minus-normalization x₊ x₋
        in
          begin
            - (x₊ -ℕ x₋)
          ≡⟨⟩
            (x₋' -ℕ x₊')
          ≡⟨← (Nat-minus-add-same x₋' x₊' kx) ⟩
            (x₋' +ℕ kx) -ℕ (x₊' +ℕ kx)
          ≡⟨← (ap2 (λ e1 e2 → e1 -ℕ e2) nx₋ nx₊) ⟩
            x₋ -ℕ x₊
          ∎

      Nat-minus-minus : (x₊ x₋ y₊ y₋ : Nat) → (x₊ -ℕ x₋) - (y₊ -ℕ y₋) ≡ (x₊ +ℕ y₋) -ℕ (x₋ +ℕ y₊)
      Nat-minus-minus x₊ x₋ y₊ y₋ =
        begin
          (x₊ -ℕ x₋) - (y₊ -ℕ y₋)
        ≡⟨⟩
          (x₊ -ℕ x₋) + (- (y₊ -ℕ y₋))
        ≡⟨ ap (λ e → (x₊ -ℕ x₋) + e) (neg-Nat-minus y₊ y₋) ⟩
          (x₊ -ℕ x₋) + (y₋ -ℕ y₊)
        ≡⟨ Nat-minus-add x₊ x₋ y₋ y₊ ⟩
          (x₊ +ℕ y₋) -ℕ (x₋ +ℕ y₊)
        ∎

      -- exercise 5.8.b
      pred-mul : (x y : Int) → pred x * y ≡ x * y - y
      pred-mul x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            pred x * y
          ≡⟨← (ap2 (λ e1 e2 → pred e1 * e2) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y)) ⟩
            pred (x₊ -ℕ x₋) * (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → e * (y₊ -ℕ y₋)) (pred-Nat-minus x₊ x₋) ⟩
            ((x₊ -ℕ (succ x₋)) * (y₊ -ℕ y₋))
          ≡⟨ Nat-minus-mul x₊ (succ x₋) y₊ y₋ ⟩
            ((x₊ *ℕ y₊) +ℕ (succ x₋ *ℕ y₋)) -ℕ
            ((x₊ *ℕ y₋) +ℕ (succ x₋ *ℕ y₊))
          ≡⟨ ap2 (λ e1 e2 → ((x₊ *ℕ y₊) +ℕ e1) -ℕ ((x₊ *ℕ y₋) +ℕ e2)) (NatCommSemiring.mul-succ-left x₋ y₋) (NatCommSemiring.mul-succ-left x₋ y₊) ⟩
            ((x₊ *ℕ y₊) +ℕ ((x₋ *ℕ y₋) +ℕ y₋)) -ℕ ((x₊ *ℕ y₋) +ℕ ((x₋ *ℕ y₊) +ℕ y₊))
          ≡⟨ ap2 (λ e1 e2 → e1 -ℕ e2) (NatCommSemiring.add-unassoc (x₊ *ℕ y₊) (x₋ *ℕ y₋) y₋) (NatCommSemiring.add-unassoc (x₊ *ℕ y₋) (x₋ *ℕ y₊) y₊) ⟩
            ((x₊ *ℕ y₊) +ℕ (x₋ *ℕ y₋) +ℕ y₋) -ℕ ((x₊ *ℕ y₋) +ℕ (x₋ *ℕ y₊) +ℕ y₊)
          ≡⟨← (Nat-minus-minus ((x₊ *ℕ y₊) +ℕ (x₋ *ℕ y₋)) ((x₊ *ℕ y₋) +ℕ (x₋ *ℕ y₊)) y₊ y₋) ⟩
            (((x₊ *ℕ y₊) +ℕ (x₋ *ℕ y₋)) -ℕ ((x₊ *ℕ y₋) +ℕ (x₋ *ℕ y₊))) - (y₊ -ℕ y₋)
          ≡⟨← (ap (λ e → e - (y₊ -ℕ y₋)) (Nat-minus-mul x₊ x₋ y₊ y₋)) ⟩
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋) - (y₊ -ℕ y₋)
          ≡⟨ ap2 (λ e1 e2 → e1 * e2 - e2) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y) ⟩
            x * y - y
          ∎

      mul-pred : (x y : Int) → x * pred y ≡ x * y - x
      mul-pred x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            x * pred y
          ≡⟨← (ap2 (λ e1 e2 → e1 * pred e2) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y)) ⟩
            (x₊ -ℕ x₋) * pred (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → (x₊ -ℕ x₋) * e) (pred-Nat-minus y₊ y₋) ⟩
            ((x₊ -ℕ x₋) * (y₊ -ℕ (succ y₋)))
          ≡⟨ Nat-minus-mul x₊ x₋ y₊ (succ y₋) ⟩
            ((x₊ *ℕ y₊) +ℕ (x₋ *ℕ (succ y₋))) -ℕ
            ((x₊ *ℕ (succ y₋)) +ℕ (x₋ *ℕ y₊))
          ≡⟨ ap2 (λ e1 e2 → ((x₊ *ℕ y₊) +ℕ e1) -ℕ (e2 +ℕ (x₋ *ℕ y₊))) (NatCommSemiring.mul-succ-right x₋ y₋) (NatCommSemiring.mul-succ-right x₊ y₋) ⟩
            (x₊ *ℕ y₊ +ℕ (x₋ +ℕ x₋ *ℕ y₋)) -ℕ (x₊ +ℕ x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊)
          ≡⟨ ap2 (λ e1 e2 → e1 -ℕ e2)
              (NatCommSemiring.add-unassoc (x₊ *ℕ y₊) x₋ (x₋ *ℕ y₋) · NatCommSemiring.add-add-rcomm (x₊ *ℕ y₊) x₋ (x₋ *ℕ y₋))
              (ap (λ e → e +ℕ (x₋ *ℕ y₊)) (NatCommSemiring.add-comm x₊ (x₊ *ℕ y₋)) · NatCommSemiring.add-add-rcomm (x₊ *ℕ y₋) x₊ (x₋ *ℕ y₊))
          ⟩
            (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋ +ℕ x₋) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊ +ℕ x₊)
          ≡⟨← (Nat-minus-minus (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) x₊ x₋) ⟩
            ((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊)) - (x₊ -ℕ x₋)
          ≡⟨← (ap (λ e → e - (x₊ -ℕ x₋)) (Nat-minus-mul x₊ x₋ y₊ y₋)) ⟩
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋) - (x₊ -ℕ x₋)
          ≡⟨ ap2 (λ e1 e2 → e1 * e2 - e1) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y) ⟩
            x * y - x
          ∎

      succ-mul : (x y : Int) → Int-succ x * y ≡ x * y + y
      succ-mul x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            Int-succ x * y
          ≡⟨← (ap2 (λ e1 e2 → Int-succ e1 * e2) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y)) ⟩
            Int-succ (x₊ -ℕ x₋) * (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → e * (y₊ -ℕ y₋)) (succ-Nat-minus x₊ x₋) ⟩
            (succ x₊ -ℕ x₋) * (y₊ -ℕ y₋)
          ≡⟨ Nat-minus-mul (succ x₊) x₋ y₊ y₋ ⟩
            ((succ x₊ *ℕ y₊) +ℕ (x₋ *ℕ y₋)) -ℕ ((succ x₊ *ℕ y₋) +ℕ (x₋ *ℕ y₊))
          ≡⟨ ap2 (λ e1 e2 → (e1 +ℕ (x₋ *ℕ y₋)) -ℕ (e2 +ℕ (x₋ *ℕ y₊))) (NatCommSemiring.mul-succ-left x₊ y₊) (NatCommSemiring.mul-succ-left x₊ y₋) ⟩
            (x₊ *ℕ y₊ +ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ y₋ +ℕ x₋ *ℕ y₊)
          ≡⟨ ap2 (λ e1 e2 → e1 -ℕ e2) (NatCommSemiring.add-add-rcomm (x₊ *ℕ y₊) y₊ (x₋ *ℕ y₋)) (NatCommSemiring.add-add-rcomm (x₊ *ℕ y₋) y₋ (x₋ *ℕ y₊)) ⟩
            (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋ +ℕ y₊) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊ +ℕ y₋)
          ≡⟨← (Nat-minus-add (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) y₊ y₋) ⟩
            ((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊)) + (y₊ -ℕ y₋)
          ≡⟨← (ap (λ e → e + (y₊ -ℕ y₋)) (Nat-minus-mul x₊ x₋ y₊ y₋)) ⟩
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋) + (y₊ -ℕ y₋)
          ≡⟨ ap3 (λ e1 e2 e3 → e1 * e2 + e3) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff y) ⟩
            x * y + y
          ∎

      mul-succ : (x y : Int) → x * Int-succ y ≡ x * y + x
      mul-succ x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            x * Int-succ y
          ≡⟨← (ap2 (λ e1 e2 → e1 * Int-succ e2) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y)) ⟩
            (x₊ -ℕ x₋) * Int-succ (y₊ -ℕ y₋)
          ≡⟨ ap (λ e → (x₊ -ℕ x₋) * e) (succ-Nat-minus y₊ y₋) ⟩
            (x₊ -ℕ x₋) * (succ y₊ -ℕ y₋)
          ≡⟨ Nat-minus-mul x₊ x₋ (succ y₊) y₋ ⟩
            ((x₊ *ℕ (succ y₊)) +ℕ (x₋ *ℕ y₋)) -ℕ ((x₊ *ℕ y₋) +ℕ (x₋ *ℕ (succ y₊)))
          ≡⟨ ap2 (λ e1 e2 → (e1 +ℕ (x₋ *ℕ y₋)) -ℕ ((x₊ *ℕ y₋) +ℕ e2))
              (NatCommSemiring.mul-succ-right x₊ y₊)
              (NatCommSemiring.mul-succ-right x₋ y₊)
          ⟩
            (x₊ +ℕ x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ (x₋ +ℕ x₋ *ℕ y₊))
          ≡⟨ ap2 (λ e1 e2 → e1 -ℕ e2)
              (ap (λ e → e +ℕ (x₋ *ℕ y₋)) (NatCommSemiring.add-comm x₊ (x₊ *ℕ y₊)) · NatCommSemiring.add-add-rcomm (x₊ *ℕ y₊) x₊ (x₋ *ℕ y₋))
              (NatCommSemiring.add-unassoc (x₊ *ℕ y₋) x₋ (x₋ *ℕ y₊) · NatCommSemiring.add-add-rcomm (x₊ *ℕ y₋) x₋ (x₋ *ℕ y₊))
          ⟩
            (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋ +ℕ x₊) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊ +ℕ x₋)
          ≡⟨← (Nat-minus-add (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) x₊ x₋) ⟩
            (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) + (x₊ -ℕ x₋)
          ≡⟨← (ap (λ e → e + (x₊ -ℕ x₋)) (Nat-minus-mul x₊ x₋ y₊ y₋)) ⟩
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋) + (x₊ -ℕ x₋)
          ≡⟨ ap3 (λ e1 e2 e3 → e1 * e2 + e3) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff x) ⟩
            x * y + x
          ∎

      -- exercise 5.8.c
      mul-ldistr : (x y z : Int) → x * (y + z) ≡ (x * y) + (x * z)
      mul-ldistr x y z =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
          (z₊ , z₋) = asNatDiff z
        in
          begin
            x * (y + z)
          ≡⟨ ap (λ e → e * (y + z)) (inverse (Nat-minus-asNatDiff x)) ⟩
            (x₊ -ℕ x₋) * ((y₊ +ℕ z₊) -ℕ (y₋ +ℕ z₋))
          ≡⟨ Nat-minus-mul x₊ x₋ (y₊ +ℕ z₊) (y₋ +ℕ z₋) ⟩
            ((x₊ *ℕ (y₊ +ℕ z₊)) +ℕ (x₋ *ℕ (y₋ +ℕ z₋))) -ℕ
            ((x₊ *ℕ (y₋ +ℕ z₋)) +ℕ (x₋ *ℕ (y₊ +ℕ z₊)))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4))
              (NatCommSemiring.mul-ldistr x₊ y₊ z₊)
              (NatCommSemiring.mul-ldistr x₋ y₋ z₋)
              (NatCommSemiring.mul-ldistr x₊ y₋ z₋)
              (NatCommSemiring.mul-ldistr x₋ y₊ z₊)
          ⟩
            ((x₊ *ℕ y₊ +ℕ x₊ *ℕ z₊) +ℕ (x₋ *ℕ y₋ +ℕ x₋ *ℕ z₋)) -ℕ
            ((x₊ *ℕ y₋ +ℕ x₊ *ℕ z₋) +ℕ (x₋ *ℕ y₊ +ℕ x₋ *ℕ z₊))
          ≡⟨ (
            let
              swapMiddle : (a b c d : Nat) → (a +ℕ b) +ℕ (c +ℕ d) ≡ (a +ℕ c) +ℕ (b +ℕ d)
              swapMiddle a b c d =
                let
                  unassoc-lhs : (a +ℕ b) +ℕ (c +ℕ d) ≡ a +ℕ b +ℕ c +ℕ d
                  unassoc-lhs = NatCommSemiring.add-unassoc (a +ℕ b) c d
                  permute : a +ℕ b +ℕ c +ℕ d ≡ a +ℕ c +ℕ b +ℕ d
                  permute = ap (λ e → e +ℕ d) (NatCommSemiring.add-add-rcomm a b c)
                  unassoc-rhs : (a +ℕ c) +ℕ (b +ℕ d) ≡ a +ℕ c +ℕ b +ℕ d
                  unassoc-rhs = NatCommSemiring.add-unassoc (a +ℕ c) b d
                in unassoc-lhs · permute · (inverse unassoc-rhs)
            in
              ap2 (λ e1 e2 → e1 -ℕ e2)
                (swapMiddle (x₊ *ℕ y₊) (x₊ *ℕ z₊) (x₋ *ℕ y₋) (x₋ *ℕ z₋))
                (swapMiddle (x₊ *ℕ y₋) (x₊ *ℕ z₋) (x₋ *ℕ y₊) (x₋ *ℕ z₊))
          ) ⟩
            ((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) +ℕ (x₊ *ℕ z₊ +ℕ x₋ *ℕ z₋)) -ℕ
            ((x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) +ℕ (x₊ *ℕ z₋ +ℕ x₋ *ℕ z₊))
          ≡⟨← (Nat-minus-add (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) (x₊ *ℕ z₊ +ℕ x₋ *ℕ z₋) (x₊ *ℕ z₋ +ℕ x₋ *ℕ z₊)) ⟩
            ((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊)) +
            ((x₊ *ℕ z₊ +ℕ x₋ *ℕ z₋) -ℕ (x₊ *ℕ z₋ +ℕ x₋ *ℕ z₊))
          ≡⟨← (ap2 (λ e1 e2 → e1 + e2) (Nat-minus-mul x₊ x₋ y₊ y₋) (Nat-minus-mul x₊ x₋ z₊ z₋)) ⟩
            ((x₊ -ℕ x₋) * (y₊ -ℕ y₋)) + ((x₊ -ℕ x₋) * (z₊ -ℕ z₋))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 * e2) + (e3 * e4)) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff z) ⟩
            (x * y) + (x * z)
          ∎

      mul-rdistr : (x y z : Int) → (x + y) * z ≡ (x * z) + (y * z)
      mul-rdistr x y z =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
          (z₊ , z₋) = asNatDiff z
        in
          begin
            (x + y) * z
          ≡⟨ ap (λ e → (x + y) * e) (inverse (Nat-minus-asNatDiff z)) ⟩
            ((x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋)) * (z₊ -ℕ z₋)
          ≡⟨ Nat-minus-mul (x₊ +ℕ y₊) (x₋ +ℕ y₋) z₊ z₋ ⟩
            (((x₊ +ℕ y₊) *ℕ z₊) +ℕ ((x₋ +ℕ y₋) *ℕ z₋)) -ℕ
            (((x₊ +ℕ y₊) *ℕ z₋) +ℕ ((x₋ +ℕ y₋) *ℕ z₊))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4))
              (NatCommSemiring.mul-rdistr x₊ y₊ z₊)
              (NatCommSemiring.mul-rdistr x₋ y₋ z₋)
              (NatCommSemiring.mul-rdistr x₊ y₊ z₋)
              (NatCommSemiring.mul-rdistr x₋ y₋ z₊)
          ⟩
            ((x₊ *ℕ z₊ +ℕ y₊ *ℕ z₊) +ℕ (x₋ *ℕ z₋ +ℕ y₋ *ℕ z₋)) -ℕ
            ((x₊ *ℕ z₋ +ℕ y₊ *ℕ z₋) +ℕ (x₋ *ℕ z₊ +ℕ y₋ *ℕ z₊))
          ≡⟨ (
            let
              swapMiddle : (a b c d : Nat) → (a +ℕ b) +ℕ (c +ℕ d) ≡ (a +ℕ c) +ℕ (b +ℕ d)
              swapMiddle a b c d =
                let
                  unassoc-lhs : (a +ℕ b) +ℕ (c +ℕ d) ≡ a +ℕ b +ℕ c +ℕ d
                  unassoc-lhs = NatCommSemiring.add-unassoc (a +ℕ b) c d
                  permute : a +ℕ b +ℕ c +ℕ d ≡ a +ℕ c +ℕ b +ℕ d
                  permute = ap (λ e → e +ℕ d) (NatCommSemiring.add-add-rcomm a b c)
                  unassoc-rhs : (a +ℕ c) +ℕ (b +ℕ d) ≡ a +ℕ c +ℕ b +ℕ d
                  unassoc-rhs = NatCommSemiring.add-unassoc (a +ℕ c) b d
                in unassoc-lhs · permute · (inverse unassoc-rhs)
            in
              ap2 (λ e1 e2 → e1 -ℕ e2)
                (swapMiddle (x₊ *ℕ z₊) (y₊ *ℕ z₊) (x₋ *ℕ z₋) (y₋ *ℕ z₋))
                (swapMiddle (x₊ *ℕ z₋) (y₊ *ℕ z₋) (x₋ *ℕ z₊) (y₋ *ℕ z₊))
          ) ⟩
            ((x₊ *ℕ z₊ +ℕ x₋ *ℕ z₋) +ℕ (y₊ *ℕ z₊ +ℕ y₋ *ℕ z₋)) -ℕ
            ((x₊ *ℕ z₋ +ℕ x₋ *ℕ z₊) +ℕ (y₊ *ℕ z₋ +ℕ y₋ *ℕ z₊))
          ≡⟨← (Nat-minus-add (x₊ *ℕ z₊ +ℕ x₋ *ℕ z₋) (x₊ *ℕ z₋ +ℕ x₋ *ℕ z₊) (y₊ *ℕ z₊ +ℕ y₋ *ℕ z₋) (y₊ *ℕ z₋ +ℕ y₋ *ℕ z₊)) ⟩
            ((x₊ *ℕ z₊ +ℕ x₋ *ℕ z₋) -ℕ (x₊ *ℕ z₋ +ℕ x₋ *ℕ z₊)) +
            ((y₊ *ℕ z₊ +ℕ y₋ *ℕ z₋) -ℕ (y₊ *ℕ z₋ +ℕ y₋ *ℕ z₊))
          ≡⟨← (ap2 (λ e1 e2 → e1 + e2) (Nat-minus-mul x₊ x₋ z₊ z₋) (Nat-minus-mul y₊ y₋ z₊ z₋)) ⟩
            ((x₊ -ℕ x₋) * (z₊ -ℕ z₋)) + ((y₊ -ℕ y₋) * (z₊ -ℕ z₋))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 * e2) + (e3 * e4)) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff z) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff z) ⟩
            (x * z) + (y * z)
          ∎

      -- exercise 5.8.d
      mul-assoc : (x y z : Int) → (x * y) * z ≡ x * (y * z)
      mul-assoc x y z =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
          (z₊ , z₋) = asNatDiff z
        in
          begin
            x * y * z
          ≡⟨← (ap3 (λ e1 e2 e3 → e1 * e2 * e3) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff z)) ⟩
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋) * (z₊ -ℕ z₋)
          ≡⟨ ap (λ e → e * (z₊ -ℕ z₋)) (Nat-minus-mul x₊ x₋ y₊ y₋) ⟩
            ((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊)) * (z₊ -ℕ z₋)
          ≡⟨ Nat-minus-mul (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) z₊ z₋ ⟩
            (((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) *ℕ z₊) +ℕ ((x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) *ℕ z₋)) -ℕ
            (((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) *ℕ z₋) +ℕ ((x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) *ℕ z₊))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4))
              (NatCommSemiring.mul-rdistr (x₊ *ℕ y₊) (x₋ *ℕ y₋) z₊)
              (NatCommSemiring.mul-rdistr (x₊ *ℕ y₋) (x₋ *ℕ y₊) z₋)
              (NatCommSemiring.mul-rdistr (x₊ *ℕ y₊) (x₋ *ℕ y₋) z₋)
              (NatCommSemiring.mul-rdistr (x₊ *ℕ y₋) (x₋ *ℕ y₊) z₊)
          ⟩
            ((x₊ *ℕ y₊ *ℕ z₊ +ℕ x₋ *ℕ y₋ *ℕ z₊) +ℕ (x₊ *ℕ y₋ *ℕ z₋ +ℕ x₋ *ℕ y₊ *ℕ z₋)) -ℕ
            ((x₊ *ℕ y₊ *ℕ z₋ +ℕ x₋ *ℕ y₋ *ℕ z₋) +ℕ (x₊ *ℕ y₋ *ℕ z₊ +ℕ x₋ *ℕ y₊ *ℕ z₊))
          ≡⟨ (
            let
              rearrange : (a b c d : Nat) → (a +ℕ b) +ℕ (c +ℕ d) ≡ (a +ℕ c) +ℕ (d +ℕ b)
              rearrange a b c d =
                let
                  unassoc-lhs : (a +ℕ b) +ℕ (c +ℕ d) ≡ a +ℕ b +ℕ c +ℕ d
                  unassoc-lhs = NatCommSemiring.add-unassoc (a +ℕ b) c d
                  permute : a +ℕ b +ℕ c +ℕ d ≡ a +ℕ c +ℕ d +ℕ b
                  permute =
                    ap (λ e → e +ℕ d) (NatCommSemiring.add-add-rcomm a b c)
                    · NatCommSemiring.add-add-rcomm (a +ℕ c) b d
                  unassoc-rhs : (a +ℕ c) +ℕ (d +ℕ b) ≡ a +ℕ c +ℕ d +ℕ b
                  unassoc-rhs = NatCommSemiring.add-unassoc (a +ℕ c) d b
                in unassoc-lhs · permute · (inverse unassoc-rhs)
              in
                ap2 (λ e1 e2 → e1 -ℕ e2)
                  (rearrange (x₊ *ℕ y₊ *ℕ z₊) (x₋ *ℕ y₋ *ℕ z₊) (x₊ *ℕ y₋ *ℕ z₋) (x₋ *ℕ y₊ *ℕ z₋))
                  (rearrange (x₊ *ℕ y₊ *ℕ z₋) (x₋ *ℕ y₋ *ℕ z₋) (x₊ *ℕ y₋ *ℕ z₊) (x₋ *ℕ y₊ *ℕ z₊))
          ) ⟩
            ((x₊ *ℕ y₊ *ℕ z₊ +ℕ x₊ *ℕ y₋ *ℕ z₋) +ℕ (x₋ *ℕ y₊ *ℕ z₋ +ℕ x₋ *ℕ y₋ *ℕ z₊)) -ℕ
            ((x₊ *ℕ y₊ *ℕ z₋ +ℕ x₊ *ℕ y₋ *ℕ z₊) +ℕ (x₋ *ℕ y₊ *ℕ z₊ +ℕ x₋ *ℕ y₋ *ℕ z₋))
          ≡⟨ ap8 (λ e1 e2 e3 e4 e5 e6 e7 e8 → ((e1 +ℕ e2) +ℕ (e3 +ℕ e4)) -ℕ ((e5 +ℕ e6) +ℕ (e7 +ℕ e8)))
              (NatCommSemiring.mul-assoc x₊ y₊ z₊) (NatCommSemiring.mul-assoc x₊ y₋ z₋)
              (NatCommSemiring.mul-assoc x₋ y₊ z₋) (NatCommSemiring.mul-assoc x₋ y₋ z₊)
              (NatCommSemiring.mul-assoc x₊ y₊ z₋) (NatCommSemiring.mul-assoc x₊ y₋ z₊)
              (NatCommSemiring.mul-assoc x₋ y₊ z₊) (NatCommSemiring.mul-assoc x₋ y₋ z₋)
          ⟩
            ((x₊ *ℕ (y₊ *ℕ z₊) +ℕ x₊ *ℕ (y₋ *ℕ z₋)) +ℕ (x₋ *ℕ (y₊ *ℕ z₋) +ℕ x₋ *ℕ (y₋ *ℕ z₊))) -ℕ
            ((x₊ *ℕ (y₊ *ℕ z₋) +ℕ x₊ *ℕ (y₋ *ℕ z₊)) +ℕ (x₋ *ℕ (y₊ *ℕ z₊) +ℕ x₋ *ℕ (y₋ *ℕ z₋)))
          ≡⟨← (ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4))
              (NatCommSemiring.mul-ldistr x₊ (y₊ *ℕ z₊) (y₋ *ℕ z₋))
              (NatCommSemiring.mul-ldistr x₋ (y₊ *ℕ z₋) (y₋ *ℕ z₊))
              (NatCommSemiring.mul-ldistr x₊ (y₊ *ℕ z₋) (y₋ *ℕ z₊))
              (NatCommSemiring.mul-ldistr x₋ (y₊ *ℕ z₊) (y₋ *ℕ z₋))
          ) ⟩
            ((x₊ *ℕ (y₊ *ℕ z₊ +ℕ y₋ *ℕ z₋)) +ℕ (x₋ *ℕ (y₊ *ℕ z₋ +ℕ y₋ *ℕ z₊))) -ℕ
            ((x₊ *ℕ (y₊ *ℕ z₋ +ℕ y₋ *ℕ z₊)) +ℕ (x₋ *ℕ (y₊ *ℕ z₊ +ℕ y₋ *ℕ z₋)))
          ≡⟨← (Nat-minus-mul x₊ x₋ (y₊ *ℕ z₊ +ℕ y₋ *ℕ z₋) (y₊ *ℕ z₋ +ℕ y₋ *ℕ z₊)) ⟩
            (x₊ -ℕ x₋) * ((y₊ *ℕ z₊ +ℕ y₋ *ℕ z₋) -ℕ (y₊ *ℕ z₋ +ℕ y₋ *ℕ z₊))
          ≡⟨ ap (λ e → (x₊ -ℕ x₋) * e) (inverse (Nat-minus-mul y₊ y₋ z₊ z₋)) ⟩
            (x₊ -ℕ x₋) * ((y₊ -ℕ y₋) * (z₊ -ℕ z₋))
          ≡⟨ ap3 (λ e1 e2 e3 → e1 * (e2 * e3)) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff z) ⟩
            x * (y * z)
          ∎

      mul-comm : (x y : Int) → x * y ≡ y * x
      mul-comm x y =
        let
          (x₊ , x₋) = asNatDiff x
          (y₊ , y₋) = asNatDiff y
        in
          begin
            x * y
          ≡⟨← (ap2 (λ e1 e2 → e1 * e2) (Nat-minus-asNatDiff x) (Nat-minus-asNatDiff y)) ⟩
            (x₊ -ℕ x₋) * (y₊ -ℕ y₋)
          ≡⟨ Nat-minus-mul x₊ x₋ y₊ y₋ ⟩
            ((x₊ *ℕ y₊) +ℕ (x₋ *ℕ y₋)) -ℕ ((x₊ *ℕ y₋) +ℕ (x₋ *ℕ y₊))
          ≡⟨ ap4 (λ e1 e2 e3 e4 → (e1 +ℕ e2) -ℕ (e3 +ℕ e4))
               (NatCommSemiring.mul-comm x₊ y₊) (NatCommSemiring.mul-comm x₋ y₋)
               (NatCommSemiring.mul-comm x₊ y₋) (NatCommSemiring.mul-comm x₋ y₊)
          ⟩
            ((y₊ *ℕ x₊ +ℕ y₋ *ℕ x₋) -ℕ (y₋ *ℕ x₊ +ℕ y₊ *ℕ x₋))
          ≡⟨ ap (λ e → (y₊ *ℕ x₊ +ℕ y₋ *ℕ x₋) -ℕ e) (NatCommSemiring.add-comm (y₋ *ℕ x₊) (y₊ *ℕ x₋)) ⟩
            ((y₊ *ℕ x₊ +ℕ y₋ *ℕ x₋) -ℕ (y₊ *ℕ x₋ +ℕ y₋ *ℕ x₊))
          ≡⟨← (Nat-minus-mul y₊ y₋ x₊ x₋) ⟩
            (y₊ -ℕ y₋) * (x₊ -ℕ x₋)
          ≡⟨ ap2 (λ e1 e2 → e1 * e2) (Nat-minus-asNatDiff y) (Nat-minus-asNatDiff x) ⟩
            y * x
          ∎
