open import Function.Base using (case_of_)

module _ where
  open import section-5 public
  
  Eq-Nat : (x y : Nat) → Set
  Eq-Nat zero zero = Unit
  Eq-Nat zero (succ y) = Empty
  Eq-Nat (succ x) zero = Empty
  Eq-Nat (succ x) (succ y) = Eq-Nat x y

  module Eq-Nat where
    open ≡-Basic

    -- 6.3.2
    Eq-Nat-refl : (n : Nat) → Eq-Nat n n
    Eq-Nat-refl zero = unit
    Eq-Nat-refl (succ n) = Eq-Nat-refl n

    -- 6.3.3
    eq-then-obseq : (x y : Nat) → (x ≡ y) → Eq-Nat x y
    eq-then-obseq x y eq = ≡-Basic.tr (λ e → Eq-Nat x e) eq (Eq-Nat-refl x)

    obseq-then-eq : (x y : Nat) → Eq-Nat x y → (x ≡ y)
    obseq-then-eq zero zero _ = refl
    obseq-then-eq zero (succ y) bot = EmptyBasic.absurd bot
    obseq-then-eq (succ x) zero bot = EmptyBasic.absurd bot
    obseq-then-eq (succ x) (succ y) eq = ap succ (obseq-then-eq x y eq)

    Nat-≡-biimpl-Eq-Nat : (x y : Nat) → ((x ≡ y) ↔ Eq-Nat x y)
    Nat-≡-biimpl-Eq-Nat x y =
      pair (eq-then-obseq x y) (obseq-then-eq x y)

  module Nat-EqualityThroughEq-Nat where
    open NatCommSemiring public
    open Eq-Nat public
    open EmptyBasic
    open NatBasic.Symbolic
    open ≡-Reasoning

    -- 6.4.1
    succ-inj : (x y : Nat) → (x ≡ y) ↔ (succ x ≡ succ y)
    succ-inj x y = pair
      (λ eq → ap succ eq)
      (λ succeq → obseq-then-eq x y (eq-then-obseq (succ x) (succ y) succeq))

    -- 6.4.2
    zero-neq-succ : (x : Nat) → ¬ (zero ≡ succ x)
    zero-neq-succ x zero-eq-succx = eq-then-obseq zero (succ x) zero-eq-succx

    -- exercise 6.1.a
    add-inj : (m n k : Nat) → (m ≡ n) ↔ (m + k ≡ n + k)
    add-inj m n k = pair
      (λ eq → ap (λ x → x + k) eq)
      (f k)
        where
        f : (k : Nat) → (m + k ≡ n + k) → (m ≡ n)
        f zero eq = eq
        f (succ k) eq = f k ((succ-inj (m + k) (n + k)).Σ.snd eq)

    add-inj-left : (m n k : Nat) → (m ≡ n) ↔ (k + m ≡ k + n)
    add-inj-left m n k = tr2 (λ e1 e2 → (m ≡ n) ↔ (e1 ≡ e2)) (add-comm m k) (add-comm n k) (add-inj m n k)

    mul-inj : (m n k : Nat) → (m ≡ n) ↔ (m * succ k ≡ n * succ k)
    mul-inj m n k = pair
      (λ eq → ap (λ x → x * succ k) eq)
      (f m n k)
        where
        f : (m n k : Nat) → (m * succ k ≡ n * succ k) → (m ≡ n)
        f m n zero eq = eq
        f zero zero (succ k) eq = refl
        f zero (succ n) (succ k) eq =
          let
            zero-eq-succ =
              begin
                zero                       ≡⟨ inverse (mul-lzero (succ (succ k))) ⟩
                zero * succ (succ k)       ≡⟨ eq ⟩
                succ n * succ (succ k)     ≡⟨⟩
                succ n + succ n * succ k   ≡⟨ add-succ-left _ _ ⟩
                succ (n + succ n * succ k)
              ∎
          in
            absurd (zero-neq-succ (n + succ n * succ k) zero-eq-succ)
        f (succ m) zero (succ k) eq =
          let
            zero-eq-succ =
              begin
                zero                       ≡⟨ inverse (mul-lzero (succ (succ k))) ⟩
                zero * succ (succ k)       ≡⟨ inverse eq ⟩
                succ m * succ (succ k)     ≡⟨⟩
                succ m + succ m * succ k   ≡⟨ add-succ-left _ _ ⟩
                succ (m + succ m * succ k)
              ∎
          in
            absurd (zero-neq-succ (m + succ m * succ k) zero-eq-succ)
        f (succ m) (succ n) (succ k) eq =
          let
            eq' =
              begin
                m * succ (succ k) + succ (succ k)   ≡⟨ inverse (mul-succ-left m (succ (succ k))) ⟩
                succ m * succ (succ k)              ≡⟨ eq ⟩
                succ n * succ (succ k)              ≡⟨ mul-succ-left n (succ (succ k)) ⟩
                n * succ (succ k) + succ (succ k)
              ∎
            eq'' = (add-inj (m * succ (succ k)) (n * succ (succ k)) (succ (succ k))).Σ.snd eq'
          in
            ap succ (f m n (succ k) eq'')

    -- exercise 6.1.b
    sum-eq-zero-iff-both-zero : (m n : Nat) → (m + n ≡ zero) ↔ ((m ≡ zero) × (n ≡ zero))
    sum-eq-zero-iff-both-zero m n = pair (forward m n) (λ { (pair refl refl) → refl })
      where
      forward : (m n : Nat) → (m + n ≡ zero) → ((m ≡ zero) × (n ≡ zero))
      forward zero zero eq = pair refl refl
      forward (succ m) zero eq = absurd (zero-neq-succ m (inverse eq))
      forward m (succ n) eq = absurd (zero-neq-succ (m + n) (inverse eq))

    product-eq-zero-iff-some-zero : (m n : Nat) → (m * n ≡ zero) ↔ ((m ≡ zero) +₁ (n ≡ zero))
    product-eq-zero-iff-some-zero m n = pair (forward m n) (λ { (left refl) → mul-lzero n ; (right refl) → mul-rzero m })
      where
      forward : (m n : Nat) → (m * n ≡ zero) → ((m ≡ zero) +₁ (n ≡ zero))
      forward m zero eq = right refl
      forward zero n eq = left refl
      forward (succ m) (succ n) eq =
        let
          eq' =
            begin
              zero                   ≡⟨ inverse eq ⟩
              succ m * succ n        ≡⟨⟩
              succ m + succ m * n    ≡⟨ add-succ-left _ _ ⟩
              succ (m + succ m * n)
            ∎
        in
          absurd (zero-neq-succ (m + succ m * n) eq')

    product-eq-one-iff-both-one : (m n : Nat) → (m * n ≡ one) ↔ ((m ≡ one) × (n ≡ one))
    product-eq-one-iff-both-one m n = pair (forward m n) (λ { (pair refl refl) → refl })
      where
      forward : (m n : Nat) → (m * n ≡ one) → ((m ≡ one) × (n ≡ one))
      forward zero zero eq = absurd (zero-neq-succ zero eq)
      forward (succ m) zero eq = absurd (zero-neq-succ zero eq)
      forward zero (succ n) eq = absurd (zero-neq-succ zero (inverse (mul-lzero (succ n)) · eq))
      forward (succ zero) (succ zero) _ = pair refl refl
      forward (succ (succ m)) (succ n) eq =
        let
          eq1 =
            begin
              succ (succ m) * succ n               ≡⟨⟩
              succ (succ m) + succ (succ m) * n    ≡⟨ add-succ-left (succ m) (succ (succ m) * n) ⟩
              succ (succ m + succ (succ m) * n)    ≡⟨ ap succ (add-succ-left m (succ (succ m) * n)) ⟩
              succ (succ (m + succ (succ m) * n))
            ∎
          eq2 =
            begin
              succ (succ (m + succ (succ m) * n))  ≡⟨ inverse eq1 ⟩
              succ (succ m) * succ n               ≡⟨ eq ⟩
              succ zero
            ∎
          eq3 = (succ-inj _ zero).Σ.snd eq2
        in absurd (zero-neq-succ _ (inverse eq3))
      forward (succ m) (succ (succ n)) eq =
        let
          eq1 =
            begin
              succ m * succ (succ n)               ≡⟨ mul-succ-left m (succ (succ n)) ⟩
              m * succ (succ n) + succ (succ n)    ≡⟨⟩
              succ (succ (m * succ (succ n) + n))
            ∎
          eq2 =
            begin
              succ (succ (m * succ (succ n) + n))  ≡⟨ inverse eq1 ⟩
              succ m * succ (succ n)               ≡⟨ eq ⟩
              succ zero
            ∎
          eq3 = (succ-inj _ zero).Σ.snd eq2
        in absurd (zero-neq-succ _ (inverse eq3))

    -- exercise 6.1.c
    self-neq-add-succ : (m n : Nat) → ¬ (m ≡ m + succ n)
    self-neq-add-succ m n eq =
      let
        eq1 = begin
          zero + m     ≡⟨ add-comm zero m ⟩
          m + zero     ≡⟨⟩
          m            ≡⟨ eq ⟩
          m + succ n   ≡⟨ add-comm m (succ n) ⟩
          succ n + m   ∎
        eq2 = (add-inj zero (succ n) m).Σ.snd eq1
      in
        absurd (zero-neq-succ _ eq2)

    self-succ-neq-mul-succ-succ : (m n : Nat) → ¬ (succ m ≡ succ m * succ (succ n))
    self-succ-neq-mul-succ-succ m n eq =
      let
        eq1 = begin
          one * succ m              ≡⟨ mul-succ-left zero (succ m) ⟩
          zero * succ m + succ m    ≡⟨ ap (λ e → e + succ m) (mul-lzero (succ m)) ⟩
          zero + succ m             ≡⟨ add-lunit (succ m) ⟩
          succ m                    ≡⟨ eq ⟩
          succ m * succ (succ n)    ≡⟨ mul-comm (succ m) _ ⟩
          succ (succ n) * succ m    ∎
        eq2 = (mul-inj one (succ (succ n)) m).Σ.snd eq1
        eq3 = (succ-inj zero (succ n)).Σ.snd eq2
      in
        absurd (zero-neq-succ _ eq3)

  Eq-Bool : (x y : Bool) → Set
  Eq-Bool false false = Unit
  Eq-Bool false true = Empty
  Eq-Bool true false = Empty
  Eq-Bool true true = Unit

  -- exercise 6.2
  module Eq-Bool where
    open BoolBasic
    open EmptyBasic
    open ≡-Basic

    Bool-≡-refl : (x : Bool) → Eq-Bool x x
    Bool-≡-refl false = unit
    Bool-≡-refl true = unit

    Bool-≡-biimpl-Eq-Bool : (x y : Bool) → ((x ≡ y) ↔ Eq-Bool x y)
    Bool-≡-biimpl-Eq-Bool x y = pair (forward x y) (backward x y)
      where
      forward : (x y : Bool) → (x ≡ y) → Eq-Bool x y
      forward x y refl = Bool-≡-refl x

      backward : (x y : Bool) → Eq-Bool x y → (x ≡ y)
      backward false false _ = refl
      backward false true bot = EmptyBasic.absurd bot
      backward true false bot = EmptyBasic.absurd bot
      backward true true _ = refl

    self-neq-neg-bool : (x : Bool) → ¬ (x ≡ neg-bool x)
    self-neq-neg-bool false eq = (Bool-≡-biimpl-Eq-Bool false true).Σ.fst eq
    self-neq-neg-bool true eq = (Bool-≡-biimpl-Eq-Bool true false).Σ.fst eq

    false-neq-true : ¬ (false ≡ true)
    false-neq-true eq = self-neq-neg-bool false eq

  Leq-Nat : (x y : Nat) → Set
  Leq-Nat zero y = Unit
  Leq-Nat (succ x) zero = Empty
  Leq-Nat (succ x) (succ y) = Leq-Nat x y

  module Leq-Nat where
    module Symbolic where
      _≤_ : Nat → Nat → Set
      _≤_ = Leq-Nat
      infix 30 _≤_  
    open Symbolic
    open ≡-Reasoning
    open NatCommSemiring
    open NatBasic.Symbolic

    Leq-Nat-refl : (n : Nat) → n ≤ n
    Leq-Nat-refl zero = unit
    Leq-Nat-refl (succ n) = Leq-Nat-refl n

    zero-leq-any : (n : Nat) → zero ≤ n
    zero-leq-any zero = unit
    zero-leq-any (succ n) = zero-leq-any n

    antisymm : (x y : Nat) → (x ≤ y) → (y ≤ x) → (x ≡ y)
    antisymm zero zero _ _ = refl
    antisymm zero (succ y) _ bot = EmptyBasic.absurd bot
    antisymm (succ x) zero bot _ = EmptyBasic.absurd bot
    antisymm (succ x) (succ y) x≤y y≤x = ap succ (antisymm x y x≤y y≤x)

    trans : (x y z : Nat) → (x ≤ y) → (y ≤ z) → (x ≤ z)
    trans zero     zero     zero     _   _   = unit
    trans zero     zero     (succ z) _   _   = unit
    trans zero     (succ y) (succ z) x≤y y≤z = trans zero y z x≤y y≤z
    trans (succ x) zero     _        bot _   = EmptyBasic.absurd bot
    trans _        (succ y) zero     _   bot = EmptyBasic.absurd bot
    trans (succ x) (succ y) (succ z) x≤y y≤z = trans x y z x≤y y≤z

    total : (x y : Nat) → (x ≤ y) +₁ (y ≤ x)
    total zero y = left unit
    total (succ x) zero = right unit
    total (succ x) (succ y) = total x y

    self-succ : (x : Nat) → (x ≤ succ x)
    self-succ zero = unit
    self-succ (succ x) = self-succ x

    self-add : (x k : Nat) → (x ≤ x + k)
    self-add x zero = Leq-Nat-refl x
    self-add x (succ k) = trans x (x + k) (x + succ k) (self-add x k) (self-succ (x + k))

    leq-biimpl-exists-diff : (x y : Nat) → (x ≤ y) ↔ (Σ Nat (λ k → x + k ≡ y))
    leq-biimpl-exists-diff x y = pair (forward x y) (backward x y)
      where
      forward : (x y : Nat) → (x ≤ y) → Σ Nat (λ k → x + k ≡ y)
      forward zero zero     _   = pair zero refl
      forward zero (succ y) _   = pair (succ y) (add-lunit (succ y)) 
      forward (succ x) zero bot = EmptyBasic.absurd bot
      forward (succ x) (succ y) succx≤succy =
        let (pair k eq) = forward x y succx≤succy
            eq' = begin
              (succ x) + k    ≡⟨ add-succ-left x k ⟩
              succ (x + k)    ≡⟨ ap succ eq ⟩
              succ y          ∎
        in (pair k eq')

      backward : (x y : Nat) → Σ Nat (λ k → x + k ≡ y) → (x ≤ y)
      backward x y (pair k refl) = self-add x k

    extract-diff : (x y : Nat) → (x ≤ y) → Σ Nat (λ k → x + k ≡ y)
    extract-diff x y x≤y = (leq-biimpl-exists-diff x y).Σ.fst x≤y

    from-diff : (x y k : Nat) → (x + k ≡ y) → (x ≤ y)
    from-diff x y k eq = (leq-biimpl-exists-diff x y).Σ.snd (pair k eq)

    leq-biimpl-add-right : (x y k : Nat) → (x ≤ y) ↔ (x + k ≤ y + k)
    leq-biimpl-add-right x y k = pair (forward x y k) (backward x y k)
      where
      forward : (x y k : Nat) → (x ≤ y) → (x + k ≤ y + k)
      forward x y zero x≤y = x≤y
      forward x y (succ k) x≤y = forward x y k x≤y

      backward : (x y k : Nat) → (x + k ≤ y + k) → (x ≤ y)
      backward x y zero x+k≤y+k = x+k≤y+k
      backward x y (succ k) x+succk≤y+succk = backward x y k x+succk≤y+succk

    leq-biimpl-add-left : (x y k : Nat) → (x ≤ y) ↔ (k + x ≤ k + y)
    leq-biimpl-add-left x y k = tr2 (λ e1 e2 → (x ≤ y) ↔ (e1 ≤ e2)) (add-comm x k) (add-comm y k) (leq-biimpl-add-right x y k)

    leq-leq-add : (a b c d : Nat) → (a ≤ b) → (c ≤ d) → (a + c ≤ b + d)
    leq-leq-add a b c d a≤b c≤d =
      let (pair b-a a+b-a=b) = extract-diff a b a≤b
          (pair d-c c+d-c=d) = extract-diff c d c≤d
          eq1 = begin
            a + c + (b-a + d-c)  ≡⟨ add-unassoc (a + c) b-a d-c ⟩
            a + c + b-a + d-c    ≡⟨ ap (λ e → e + d-c) (add-add-rcomm a c b-a) ⟩
            a + b-a + c + d-c    ≡⟨ ap (λ e → e + c + d-c) a+b-a=b ⟩
            b + c + d-c          ≡⟨ add-assoc b c _ ⟩
            b + (c + d-c)        ≡⟨ ap (λ e → b + e) c+d-c=d ⟩
            b + d                ∎
      in from-diff (a + c) (b + d) (b-a + d-c) eq1

    leq-biimpl-mul-succ : (x y k : Nat) → (x ≤ y) ↔ (x * succ k ≤ y * succ k)
    leq-biimpl-mul-succ x y k = pair (forward' x y (succ k)) (backward x y k)
      where
      forward' : (x y k : Nat) → (x ≤ y) → (x * k ≤ y * k)
      forward' x y k x≤y =
        let (pair y-x eq) = extract-diff x y x≤y
            eq' = begin
              y * k              ≡⟨ ap (λ e → e * k) (inverse eq) ⟩
              (x + y-x) * k      ≡⟨ mul-rdistr x y-x k ⟩
              x * k + y-x * k    ∎
        in from-diff (x * k) (y * k) (y-x * k) (inverse eq')

      backward : (x y k : Nat) → (x * succ k ≤ y * succ k) → (x ≤ y)
      backward zero     zero     _ _   = unit
      backward zero     (succ y) _ _   = unit 
      backward (succ x) zero     k leq =
        EmptyBasic.absurd (tr2 (λ e1 e2 → e1 ≤ e2)
          (add-succ-left x (succ x * k))
          (mul-lzero (succ k)) leq)
      backward (succ x) (succ y) k leq =
        let leq1 : x * succ k + succ k ≤ y * succ k + succ k
            leq1 = tr2 (λ e1 e2 → e1 ≤ e2) (mul-succ-left x (succ k)) (mul-succ-left y (succ k)) leq

            leq2 : x * succ k ≤ y * succ k
            leq2 = (leq-biimpl-add-right (x * succ k) (y * succ k) (succ k)).Σ.snd leq1
        in backward x y k leq2

    leq-add-succ-right : (x y : Nat) → (x + y ≤ x + succ y)
    leq-add-succ-right x y = self-succ (x + y)

    leq-add-succ-left : (x y : Nat) → (x + y ≤ succ x + y)
    leq-add-succ-left x y = tr (λ e → x + y ≤ e) (inverse (add-succ-left x y)) (self-succ (x + y))

    module Min-Leq where
      leq-then-min-eq : (m n : Nat) → (m ≤ n) → (min m n ≡ m)
      leq-then-min-eq zero zero _ = refl
      leq-then-min-eq zero (succ n) _ = refl
      leq-then-min-eq (succ m) zero ()
      leq-then-min-eq (succ m) (succ n) sm≤sn = ap succ (leq-then-min-eq m n sm≤sn)

      min-leq-left : (m n : Nat) → (min m n ≤ m)
      min-leq-left zero zero = unit
      min-leq-left zero (succ n) = unit
      min-leq-left (succ m) zero = zero-leq-any (succ m)
      min-leq-left (succ m) (succ n) = min-leq-left m n

      min-symm : (m n : Nat) → (min m n ≡ min n m)
      min-symm zero zero = refl
      min-symm zero (succ n) = refl
      min-symm (succ m) zero = refl
      min-symm (succ m) (succ n) = ap succ (min-symm m n)

      min-leq-right : (m n : Nat) → (min m n ≤ n)
      min-leq-right m n = tr (λ e → e ≤ n) (min-symm n m) (min-leq-left n m)

      leq-min-biimpl-leq-both : (m n k : Nat) → (m ≤ min n k) ↔ ((m ≤ n) × (m ≤ k))
      leq-min-biimpl-leq-both m n k = pair forward (backward m n k)
        where
        forward : (m ≤ min n k) → ((m ≤ n) × (m ≤ k))
        forward m≤minnk =
          pair
            (trans m (min n k) n m≤minnk (min-leq-left n k))
            (trans m (min n k) k m≤minnk (min-leq-right n k))

        backward : (m n k : Nat) → ((m ≤ n) × (m ≤ k)) → (m ≤ min n k)
        backward m n k (pair m≤n m≤k) =
          case (total n k) of λ {
            (left n≤k) → tr (λ e → m ≤ e) (inverse (leq-then-min-eq n k n≤k)) m≤n
          ; (right k≤n) → tr (λ e → m ≤ e) (inverse (min-symm n k · leq-then-min-eq k n k≤n)) m≤k
          }

    module Max-Leq where
      leq-then-max-eq : (m n : Nat) → (m ≤ n) → (max m n ≡ n)
      leq-then-max-eq zero zero _ = refl
      leq-then-max-eq zero (succ n) _ = refl
      leq-then-max-eq (succ m) zero ()
      leq-then-max-eq (succ m) (succ n) sm≤sn = ap succ (leq-then-max-eq m n sm≤sn)

      max-leq-left : (m n : Nat) → (m ≤ max m n)
      max-leq-left zero zero = unit
      max-leq-left zero (succ n) = zero-leq-any (succ n)
      max-leq-left (succ m) zero = Leq-Nat-refl (succ m)
      max-leq-left (succ m) (succ n) = max-leq-left m n

      max-symm : (m n : Nat) → (max m n ≡ max n m)
      max-symm zero zero = refl
      max-symm zero (succ n) = refl
      max-symm (succ m) zero = refl
      max-symm (succ m) (succ n) = ap succ (max-symm m n)

      max-leq-right : (m n : Nat) → (n ≤ max m n)
      max-leq-right m n = tr (λ e → n ≤ e) (max-symm n m) (max-leq-left n m)

      max-leq-biimpl-leq-both : (m n k : Nat) → (max m n ≤ k) ↔ ((m ≤ k) × (n ≤ k))
      max-leq-biimpl-leq-both m n k = pair forward (backward m n k)
        where
        forward : (max m n ≤ k) → ((m ≤ k) × (n ≤ k))
        forward max≤k =
          pair
            (trans m (max m n) k (max-leq-left m n) max≤k)
            (trans n (max m n) k (max-leq-right m n) max≤k)
        backward : (m n k : Nat) → ((m ≤ k) × (n ≤ k)) → (max m n ≤ k)
        backward m n k (pair m≤k n≤k) =
          case (total m n) of λ {
            (left m≤n) → tr (λ e → e ≤ k) (inverse (leq-then-max-eq m n m≤n)) n≤k
          ; (right n≤m) → tr (λ e → e ≤ k) (inverse (max-symm m n · leq-then-max-eq n m n≤m)) m≤k
          }

      max-leq-add : (a b : Nat) → max a b ≤ a + b
      max-leq-add a b =
        case (total a b) of λ {
          (left a≤b) → from-diff (max a b) (a + b) a (begin
            max a b + a   ≡⟨ ap (λ e → e + a) (leq-then-max-eq a b a≤b) ⟩
            b + a         ≡⟨ add-comm b a ⟩
            a + b         ∎
          )
        ; (right b≤a) → from-diff (max a b) (a + b) b (
            max a b + b   ≡⟨ ap (λ e → e + b) (max-symm a b · leq-then-max-eq b a b≤a) ⟩
            a + b         ∎
          )
        }

  Lt-Nat : (x y : Nat) → Set
  Lt-Nat zero zero = Empty
  Lt-Nat zero (succ y) = Unit
  Lt-Nat (succ x) zero = Empty
  Lt-Nat (succ x) (succ y) = Lt-Nat x y

  module Lt-Nat where
    module Symbolic where
      _<_ : Nat → Nat → Set
      _<_ = Lt-Nat
      infix 30 _<_
    open Symbolic
    open ≡-Reasoning
    open EmptyBasic
    open NatCommSemiring
    open NatBasic.Symbolic
    open Leq-Nat.Symbolic

    antireflexive : (x : Nat) → ¬ (x < x)
    antireflexive zero ()
    antireflexive (succ x) bot = EmptyBasic.absurd (antireflexive x bot)

    asymmetric : (x y : Nat) → (x < y) → ¬ (y < x)
    asymmetric zero zero ()
    asymmetric (succ x) zero ()
    asymmetric zero (succ y) zero<sy ()
    asymmetric (succ x) (succ y) sx<sy sy<sx = EmptyBasic.absurd (asymmetric x y sx<sy sy<sx)

    trans : (x y z : Nat) → (x < y) → (y < z) → (x < z)
    trans zero     zero     z ()
    trans zero     (succ y) zero zero<sy ()
    trans zero     (succ y) (succ z) zero<sy sy<sz = unit
    trans (succ x) zero     z ()
    trans (succ x) (succ y) zero sx<sy ()
    trans (succ x) (succ y) (succ z) sx<sy sy<sz = trans x y z sx<sy sy<sz

    lt-succ : (x : Nat) → (x < succ x)
    lt-succ zero = unit
    lt-succ (succ x) = lt-succ x

    not-lt-zero : (x : Nat) → ¬ (x < zero)
    not-lt-zero zero ()
    not-lt-zero (succ x) ()

    lt-then-lt-succ : (x y : Nat) → (x < y) → (x < succ y)
    lt-then-lt-succ x y x<y = trans x y (succ y) x<y (lt-succ y)
    
    self-lt-succ : (x : Nat) → (x < succ x)
    self-lt-succ zero = unit
    self-lt-succ (succ x) = self-lt-succ x

    self-add-succ : (x k : Nat) → (x < x + succ k)
    self-add-succ x zero = self-lt-succ x
    self-add-succ x (succ k) = trans x (x + succ k) (x + succ (succ k)) (self-add-succ x k) (self-lt-succ (x + succ k))

    lt-biimpl-exists-diff : (x y : Nat) → (x < y) ↔ (Σ Nat (λ k → x + succ k ≡ y))
    lt-biimpl-exists-diff x y = pair (forward x y) (backward x y)
      where
      forward : (x y : Nat) → (x < y) → Σ Nat (λ k → x + succ k ≡ y)
      forward zero     zero     ()
      forward zero     (succ y) _ = pair y (add-lunit (succ y))
      forward (succ x) zero ()
      forward (succ x) (succ y) sx<sy =
        let (pair k eq) = forward x y sx<sy
            eq' = begin
              succ x + succ k      ≡⟨ add-succ-left x (succ k) ⟩
              succ (x + succ k)    ≡⟨ ap succ eq ⟩
              succ y                ∎
        in (pair k eq')

      backward : (x y : Nat) → Σ Nat (λ k → x + succ k ≡ y) → (x < y)
      backward x y (pair k refl) = self-add-succ x k

    extract-diff : (x y : Nat) → (x < y) → Σ Nat (λ k → x + succ k ≡ y)
    extract-diff x y x<y = (lt-biimpl-exists-diff x y).Σ.fst x<y

    from-diff : (x y k : Nat) → (x + succ k ≡ y) → (x < y)
    from-diff x y k eq = (lt-biimpl-exists-diff x y).Σ.snd (pair k eq)

    lt-biimpl-succ-leq : (m n : Nat) → (m < n) ↔ (succ m ≤ n)
    lt-biimpl-succ-leq m n = pair forward backward
      where
      forward : (m < n) → (succ m ≤ n)
      forward m<n =
        let (pair k m+sk≡n) = extract-diff m n m<n
            eq = begin
              succ m + k     ≡⟨ add-succ-left m k ⟩
              succ (m + k)   ≡⟨⟩
              m + succ k     ≡⟨ m+sk≡n ⟩
              n              ∎
        in Leq-Nat.from-diff (succ m) n k eq

      backward : (succ m ≤ n) → (m < n)
      backward succm≤n =
        let (pair k succm+k≡n) = Leq-Nat.extract-diff (succ m) n succm≤n
            eq = begin
              m + succ k     ≡⟨⟩
              succ (m + k)   ≡⟨ inverse (add-succ-left m k) ⟩
              succ m + k     ≡⟨ succm+k≡n ⟩
              n              ∎
        in from-diff m n k eq

    trichotomy : (m n : Nat) → (m < n) +₁ (m ≡ n) +₁ (n < m)
    trichotomy zero zero = left (right refl)
    trichotomy zero (succ n) = left (left unit)
    trichotomy (succ m) zero = right unit
    trichotomy (succ m) (succ n) =
      case (trichotomy m n) of λ {
        (left (left m<n)) → left (left m<n)
      ; (left (right m≡n)) → left (right (ap succ m≡n))
      ; (right n<m) → right n<m
      }

    lt-or-eq-biimpl-leq : (m n : Nat) → ((m < n) +₁ (m ≡ n)) ↔ (m ≤ n)
    lt-or-eq-biimpl-leq m n = pair forward backward
      where
      forward : ((m < n) +₁ (m ≡ n)) → (m ≤ n)
      forward (left m<n) =
        let (pair k m+sk≡n) = extract-diff m n m<n
        in Leq-Nat.from-diff m n (succ k) m+sk≡n
      forward (right refl) = Leq-Nat.Leq-Nat-refl m

      backward : (m ≤ n) → ((m < n) +₁ (m ≡ n))
      backward m≤n with Leq-Nat.extract-diff m n m≤n
      ...             | (pair zero m+zero≡n) = right m+zero≡n
      ...             | (pair (succ k) m+sk≡n) = left (from-diff m n k m+sk≡n)

    lt-biimpl-not-flip-leq : (m n : Nat) → (m < n) ↔ ¬ (n ≤ m)
    lt-biimpl-not-flip-leq m n = pair (forward m n) backward
      where
      forward : (m n : Nat) → (m < n) → ¬ (n ≤ m)
      forward zero zero ()
      forward zero (succ n) z<sn ()
      forward (succ m) zero ()
      forward (succ m) (succ n) sm<sn sn≤sm = forward m n sm<sn sn≤sm

      backward : ¬ (n ≤ m) → (m < n)
      backward notn≤m =
        case (trichotomy m n) of λ {
          (left (left m<n)) → m<n
        ; (left (right m≡n)) → absurd (notn≤m ((lt-or-eq-biimpl-leq n m).Σ.fst (right (inverse m≡n))))
        ; (right n<m) → absurd (notn≤m ((lt-or-eq-biimpl-leq n m).Σ.fst (left n<m)))
        }
    
    as-leq : (m n : Nat) → (m < n) → (m ≤ n)
    as-leq m n m<n = (lt-or-eq-biimpl-leq m n).Σ.fst (left m<n)


  Nat-dist : (m n : Nat) → Nat
  Nat-dist zero zero = zero
  Nat-dist zero (succ n) = succ n
  Nat-dist (succ m) zero = succ m
  Nat-dist (succ m) (succ n) = Nat-dist m n

  module Nat-dist where
    open ≡-Reasoning
    open EmptyBasic
    open NatCommSemiring
    open Nat-EqualityThroughEq-Nat
    open Leq-Nat
    open NatBasic.Symbolic
    open Leq-Nat.Symbolic

    dist-to-zero : (x : Nat) → (Nat-dist x zero ≡ x)
    dist-to-zero zero = refl
    dist-to-zero (succ x) = refl

    dist-from-zero : (x : Nat) → (Nat-dist zero x ≡ x)
    dist-from-zero zero = refl
    dist-from-zero (succ x) = refl

    translation-inv : (a m n : Nat) → Nat-dist (a + m) (a + n) ≡ Nat-dist m n
    translation-inv zero m n = ap2 (λ e1 e2 → Nat-dist e1 e2) (add-lunit m) (add-lunit n)
    translation-inv (succ a) m n = begin
      Nat-dist (succ a + m) (succ a + n)  ≡⟨ ap2 (λ e1 e2 → Nat-dist e1 e2) (add-succ-left a m) (add-succ-left a n) ⟩
      Nat-dist (a + m) (a + n)            ≡⟨ translation-inv a m n ⟩
      Nat-dist m n                        ∎

    bounded : (m n : Nat) → (Nat-dist m n ≤ max m n)
    bounded zero zero = Leq-Nat-refl zero
    bounded zero (succ n) = Leq-Nat-refl (succ n)
    bounded (succ m) zero = Leq-Nat-refl (succ m)
    bounded (succ m) (succ n) = Leq-Nat.trans (Nat-dist m n) (max m n) (succ (max m n)) (bounded m n) (self-succ (max m n))

    module Metric where
      dist-to-self-eq-zero : (x : Nat) → (Nat-dist x x ≡ zero)
      dist-to-self-eq-zero zero = refl
      dist-to-self-eq-zero (succ x) = dist-to-self-eq-zero x

      positivity : (m n : Nat) → (m ≡ n) ↔ (Nat-dist m n ≡ zero)
      positivity m n = pair forward (backward m n)
        where
        forward : m ≡ n → Nat-dist m n ≡ zero
        forward refl = dist-to-self-eq-zero m

        backward : (m n : Nat) → Nat-dist m n ≡ zero → m ≡ n
        backward zero zero eq = refl
        backward zero (succ n) eq = absurd (zero-neq-succ n (inverse eq))
        backward (succ m) zero eq = absurd (zero-neq-succ m (inverse eq))
        backward (succ m) (succ n) eq = ap succ (backward m n eq)

      symm : (m n : Nat) → (Nat-dist m n ≡ Nat-dist n m)
      symm zero zero = refl
      symm zero (succ n) = refl
      symm (succ m) zero = refl
      symm (succ m) (succ n) = symm m n

      -- lemma needed for triangle inequality
      leq-dist-add : (m n : Nat) → m ≤ Nat-dist m n + n
      leq-dist-add zero zero = Leq-Nat-refl zero
      leq-dist-add zero (succ n) = zero-leq-any (Nat-dist zero (succ n) + succ n)
      leq-dist-add (succ m) zero = Leq-Nat-refl (succ m)
      leq-dist-add (succ m) (succ n) = leq-dist-add m n

      triangle : (m n k : Nat) → (Nat-dist m n ≤ Nat-dist m k + Nat-dist k n)
      triangle zero zero zero = from-diff zero zero zero refl
      triangle zero zero (succ k) = zero-leq-any (succ k + succ k)
      triangle zero (succ n) zero = from-diff (succ n) (zero + succ n) zero (inverse (add-lunit (succ n)))
      triangle zero (succ n) (succ k) =
        tr
          (λ e → succ n ≤ e)
          (begin
            Nat-dist n k + succ k                   ≡⟨ ap (λ e → e + succ k) (symm n k) ⟩
            Nat-dist k n + succ k                   ≡⟨⟩
            Nat-dist (succ k) (succ n) + succ k     ≡⟨ add-comm (Nat-dist (succ k) (succ n)) (succ k) ⟩
            succ k + Nat-dist (succ k) (succ n)     ∎
          )
          (leq-dist-add (succ n) (succ k))
      triangle (succ m) zero zero = Leq-Nat-refl (succ m)
      triangle (succ m) zero (succ k) = leq-dist-add (succ m) (succ k)
      triangle (succ m) (succ n) zero =
        trans (Nat-dist m n) _ _ (bounded m n) (
          trans (max m n) _ _ (Max-Leq.max-leq-add m n) (
            trans (m + n) _ _
              (leq-add-succ-right m n)
              (leq-add-succ-left m (succ n))
          )
        )
      triangle (succ m) (succ n) (succ k) = triangle m n k

    ordered-then-diff : (m n : Nat) → (m ≤ n) → m + Nat-dist m n ≡ n
    ordered-then-diff zero zero _ = refl
    ordered-then-diff zero (succ n) _ = add-lunit (succ n)
    ordered-then-diff (succ m) zero ()
    ordered-then-diff (succ m) (succ n) sm≤sn = (add-succ-left m (Nat-dist m n)) · (ap succ (ordered-then-diff m n sm≤sn))

    triangle-eq-biimpl-ordered : (m n k : Nat) →
                                 (Nat-dist m n ≡ Nat-dist m k + Nat-dist k n) ↔ 
                                 (((m ≤ k) × (k ≤ n)) +₁ ((n ≤ k) × (k ≤ m)))
    triangle-eq-biimpl-ordered m n k = pair forward backward
      where
        forward : (Nat-dist m n ≡ Nat-dist m k + Nat-dist k n) → (((m ≤ k) × (k ≤ n)) +₁ ((n ≤ k) × (k ≤ m)))
        forward eqn =
          case (Lt-Nat.trichotomy m k) of λ {
            (left (left m<k)) →
              left (pair
                (Lt-Nat.as-leq m k m<k)
                (case (Lt-Nat.trichotomy k n) of λ {
                  (left (left k<n)) → Lt-Nat.as-leq k n k<n
                ; (left (right refl)) → Leq-Nat-refl n
                ; (right n<k) → -- we have m<k, n<k and yet eqn, so this should lead to a contradiction
                    {!   !}
                })
              )
          ; (right k<m) →
              right (pair
                (case (Lt-Nat.trichotomy n k) of λ {
                  (left (left n<k)) → Lt-Nat.as-leq n k n<k
                ; (left (right refl)) → Leq-Nat-refl k
                ; (right k<n) → -- we have k<m, k<n and yet eqn, so this should lead to a contradiction
                    {!   !}
                })
                (Lt-Nat.as-leq k m k<m)
              )
          ; (left (right refl)) → case (total m n) of λ {
              (left m≤n) → left (pair (Leq-Nat-refl m) m≤n)
            ; (right n≤m) → right (pair n≤m (Leq-Nat-refl m))
            }
          }

        backward' : (m n k : Nat) → ((m ≤ k) × (k ≤ n)) → Nat-dist m n ≡ Nat-dist m k + Nat-dist k n
        backward' m n k (pair m≤k k≤n) =
          inverse ((add-inj-left (Nat-dist m k + Nat-dist k n) (Nat-dist m n) m).Σ.snd lemma)
            where
            lemma : m + (Nat-dist m k + Nat-dist k n) ≡ m + Nat-dist m n
            lemma = begin
              m + (Nat-dist m k + Nat-dist k n)    ≡⟨ add-unassoc m (Nat-dist m k) (Nat-dist k n) ⟩
              m + Nat-dist m k + Nat-dist k n      ≡⟨ ap (λ e → e + Nat-dist k n) (ordered-then-diff m k m≤k) ⟩
              k + Nat-dist k n                     ≡⟨ ordered-then-diff k n k≤n ⟩
              n                                    ≡⟨ inverse (ordered-then-diff m n (trans m k n m≤k k≤n)) ⟩
              m + Nat-dist m n                     ∎          

        backward : (((m ≤ k) × (k ≤ n)) +₁ ((n ≤ k) × (k ≤ m))) → (Nat-dist m n ≡ Nat-dist m k + Nat-dist k n)
        backward (left (pair m≤k k≤n)) = backward' m n k (pair m≤k k≤n)
        backward (right (pair n≤k k≤m)) = begin
          Nat-dist m n                  ≡⟨ Metric.symm m n ⟩
          Nat-dist n m                  ≡⟨ backward' n m k (pair n≤k k≤m) ⟩
          Nat-dist n k + Nat-dist k m   ≡⟨ ap2 (λ e1 e2 → e1 + e2) (Metric.symm n k) (Metric.symm k m) ⟩
          Nat-dist k n + Nat-dist m k   ≡⟨ add-comm (Nat-dist k n) (Nat-dist m k) ⟩
          Nat-dist m k + Nat-dist k n   ∎

    ordered-dist-add-eq-right-add : (a b c : Nat) → (a ≤ b) → (Nat-dist a b + c ≡ Nat-dist a (b + c))
    ordered-dist-add-eq-right-add a b c a≤b =
      let
        eq = begin
          a + (Nat-dist a b + c)   ≡⟨ add-unassoc a (Nat-dist a b) c ⟩
          a + Nat-dist a b + c     ≡⟨ ap (λ e → e + c) (ordered-then-diff a b a≤b) ⟩
          b + c                    ≡⟨ inverse (ordered-then-diff a (b + c) (trans a b (b + c) a≤b (self-add b c))) ⟩
          a + Nat-dist a (b + c)   ∎
      in (add-inj-left (Nat-dist a b + c) (Nat-dist a (b + c)) a).Σ.snd eq

    add-same-order : (a b c d : Nat) → ((a ≤ b) ↔ (c ≤ d)) → (Nat-dist a b + Nat-dist c d ≡ Nat-dist (a + c) (b + d))
    add-same-order a b zero zero _ = refl
    add-same-order a b zero (succ d) (pair _ c≤dthena≤b) = 
      let a≤b = c≤dthena≤b (Leq-Nat.zero-leq-any d)
      in ordered-dist-add-eq-right-add a b (succ d) a≤b
    add-same-order a b (succ c) zero (pair a≤bthensc≤zero _) =
      let
        b<a = case (Lt-Nat.trichotomy a b) of λ {
            (left (left a<b)) → absurd (a≤bthensc≤zero (Lt-Nat.as-leq a b a<b))
          ; (left (right refl)) → absurd (a≤bthensc≤zero (Leq-Nat-refl a))
          ; (right b<a) → b<a
          }
      in begin
        Nat-dist a b + Nat-dist (succ c) zero    ≡⟨⟩
        Nat-dist a b + succ c                    ≡⟨ ap (λ e → e + succ c) (Metric.symm a b) ⟩
        Nat-dist b a + succ c                    ≡⟨ ordered-dist-add-eq-right-add b a (succ c) (Lt-Nat.as-leq b a b<a) ⟩
        Nat-dist b (a + succ c)                  ≡⟨ Metric.symm b (a + succ c) ⟩
        Nat-dist (a + succ c) b                  ∎
    add-same-order a b (succ c) (succ d) eqn = add-same-order a b c d eqn

    right-succ-leq-succ : (a b : Nat) → Nat-dist a (succ b) ≤ succ (Nat-dist a b)
    right-succ-leq-succ zero b = tr (λ e → Nat-dist zero (succ b) ≤ succ e) (inverse (dist-from-zero b)) (Leq-Nat-refl (succ b))
    right-succ-leq-succ (succ a) zero =
      trans (Nat-dist a zero) (succ a) (succ (succ a))
        (tr (λ e → e ≤ succ a) (inverse (dist-to-zero a)) (self-succ a))
        (self-succ (succ a))
    right-succ-leq-succ (succ a) (succ b) = right-succ-leq-succ a b

    right-add-leq-add : (a b c : Nat) → Nat-dist a (b + c) ≤ Nat-dist a b + c
    right-add-leq-add a b zero = Leq-Nat-refl (Nat-dist a b)
    right-add-leq-add a b (succ c) =
      trans (Nat-dist a (b + succ c)) (succ (Nat-dist a (b + c))) (Nat-dist a b + succ c)
        (right-succ-leq-succ a (b + c))
        (right-add-leq-add a b c)

    left-succ-leq-succ : (a b : Nat) → Nat-dist (succ a) b ≤ succ (Nat-dist a b)
    left-succ-leq-succ a b = tr2 (λ e1 e2 → e1 ≤ succ e2) (Metric.symm b (succ a)) (Metric.symm b a) (right-succ-leq-succ b a)

    left-add-leq-add : (a b c : Nat) → Nat-dist (a + c) b ≤ Nat-dist a b + c
    left-add-leq-add a b c = tr2 (λ e1 e2 → e1 ≤ e2 + c) (Metric.symm b (a + c)) (Metric.symm b a) (right-add-leq-add b a c)

    cross-add-leq-add : (a b c d : Nat) → Nat-dist (a + c) (b + d) ≤ Nat-dist a b + Nat-dist c d
    cross-add-leq-add a b zero zero = Leq-Nat-refl (Nat-dist a b)
    cross-add-leq-add a b zero (succ d) =
      trans (Nat-dist a (succ (b + d))) (succ (Nat-dist a (b + d))) (succ (Nat-dist a b + d))
        (right-succ-leq-succ a (b + d))
        (right-add-leq-add a b d)
    cross-add-leq-add a b (succ c) zero =
      trans (Nat-dist (succ (a + c)) b) (succ (Nat-dist (a + c) b)) (succ (Nat-dist a b + c))
        (left-succ-leq-succ (a + c) b)
        (left-add-leq-add a b c)
    cross-add-leq-add a b (succ c) (succ d) = cross-add-leq-add a b c d

    cross-mul-leq-mul : (a b c d : Nat) → Nat-dist (a * c + b * d) (a * d + b * c) ≤ Nat-dist a b * Nat-dist c d
    cross-mul-leq-mul = {!   !}

    linear : (k m n : Nat) → Nat-dist (k * m) (k * n) ≡ k * Nat-dist m n
    linear zero m n = begin
      Nat-dist (zero * m) (zero * n)  ≡⟨ ap2 (λ e1 e2 → Nat-dist e1 e2) (mul-lzero m) (mul-lzero n) ⟩
      Nat-dist zero zero              ≡⟨⟩
      zero                            ≡⟨ inverse (mul-lzero (Nat-dist m n)) ⟩
      zero * Nat-dist m n             ∎
    linear (succ k) m n = begin
      Nat-dist (succ k * m) (succ k * n)         ≡⟨ ap2 (λ e1 e2 → Nat-dist e1 e2) (mul-succ-left k m) (mul-succ-left k n) ⟩
      Nat-dist (k * m + m) (k * n + n)           ≡⟨ equality k ⟩
      Nat-dist (k * m) (k * n) + Nat-dist m n    ≡⟨ ap (λ e → e + Nat-dist m n) (linear k m n) ⟩
      k * Nat-dist m n + Nat-dist m n            ≡⟨ inverse (mul-succ-left k (Nat-dist m n)) ⟩
      succ k * Nat-dist m n                      ∎
        where
          equality : (k : Nat) → Nat-dist (k * m + m) (k * n + n) ≡ Nat-dist (k * m) (k * n) + Nat-dist m n
          equality zero = begin
            Nat-dist (zero * m + m) (zero * n + n)           ≡⟨ ap2 (λ e1 e2 → Nat-dist (e1 + m) (e2 + n)) (mul-lzero m) (mul-lzero n) ⟩
            Nat-dist (zero + m) (zero + n)                   ≡⟨ ap2 (λ e1 e2 → Nat-dist e1 e2) (add-lunit m) (add-lunit n) ⟩
            Nat-dist m n                                     ≡⟨ inverse (add-lunit (Nat-dist m n)) ⟩
            zero + Nat-dist m n                              ≡⟨⟩
            Nat-dist zero zero + Nat-dist m n                ≡⟨ ap2 (λ e1 e2 → Nat-dist e1 e2 + Nat-dist m n) (inverse (mul-lzero m)) (inverse (mul-lzero n)) ⟩
            Nat-dist (zero * m) (zero * n) + Nat-dist m n    ∎

          equality (succ k) =
            inverse (add-same-order (succ k * m) (succ k * n) m n (
              ↔-Basic.flip-biimpl (tr2 (λ e1 e2 → (m ≤ n) ↔ (e1 ≤ e2))
                (mul-comm m (succ k))
                (mul-comm n (succ k))
                (leq-biimpl-mul-succ m n k)
              )
            ))

  Int-abs : (x : Int) → Nat
  Int-abs zeroInt = zero
  Int-abs (posSucc x) = succ x
  Int-abs (negSucc x) = succ x

  module Int-abs where
    open EmptyBasic
    open IntEquality.IntCommRing
    open NatBasic.SymbolicQualified
    open IntBasic.Symbolic
    open IntBasic.SymbolicQualified
    open ≡-Reasoning
    open Leq-Nat
    open Leq-Nat.Symbolic

    positive-definite : (x : Int) → (x ≡ zeroInt) ↔ (Int-abs x ≡ zero)
    positive-definite x = pair forward (backward x)
      where
      forward : (x ≡ zeroInt) → (Int-abs x ≡ zero)
      forward refl = refl

      backward : (x : Int) → (Int-abs x ≡ zero) → (x ≡ zeroInt)
      backward zeroInt zeroInt≡zero = refl
      backward (posSucc x) ()
      backward (negSucc x) ()

    abs-Nat-minus : (x₊ x₋ : Nat) → Int-abs (x₊ -ℕ x₋) ≡ Nat-dist x₊ x₋
    abs-Nat-minus zero zero = refl
    abs-Nat-minus zero (succ x₋) = refl
    abs-Nat-minus (succ x₊) zero = refl
    abs-Nat-minus (succ x₊) (succ x₋) = abs-Nat-minus x₊ x₋

    triangle : (x y : Int) → Int-abs (x + y) ≤ Int-abs x +ℕ Int-abs y
    triangle x y =
      let
        (pair x₊ x₋) = asNatDiff x
        (pair y₊ y₋) = asNatDiff y
        lhs : Int-abs (x + y) ≡ Nat-dist (x₊ +ℕ y₊) (x₋ +ℕ y₋)
        lhs = begin
          Int-abs (x + y)                      ≡⟨ ap2 (λ e1 e2 → Int-abs (e1 + e2)) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
          Int-abs ((x₊ -ℕ x₋) + (y₊ -ℕ y₋))    ≡⟨ ap Int-abs (Nat-minus-add x₊ x₋ y₊ y₋) ⟩
          Int-abs ((x₊ +ℕ y₊) -ℕ (x₋ +ℕ y₋))   ≡⟨ abs-Nat-minus (x₊ +ℕ y₊) (x₋ +ℕ y₋) ⟩
          Nat-dist (x₊ +ℕ y₊) (x₋ +ℕ y₋)       ∎
        rhs : Int-abs x +ℕ Int-abs y ≡ Nat-dist x₊ x₋ +ℕ Nat-dist y₊ y₋
        rhs = begin
          Int-abs x +ℕ Int-abs y                     ≡⟨ ap2 (λ e1 e2 → Int-abs e1 +ℕ Int-abs e2) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
          Int-abs (x₊ -ℕ x₋) +ℕ Int-abs (y₊ -ℕ y₋)   ≡⟨ ap2 (λ e1 e2 → e1 +ℕ e2) (abs-Nat-minus x₊ x₋) (abs-Nat-minus y₊ y₋) ⟩
          Nat-dist x₊ x₋ +ℕ Nat-dist y₊ y₋           ∎
      in tr2 (λ e1 e2 → e1 ≤ e2) (inverse lhs) (inverse rhs) (Nat-dist.cross-add-leq-add x₊ x₋ y₊ y₋)

    preserves-prod : (x y : Int) → Int-abs (x * y) ≤ Int-abs x *ℕ Int-abs y
    preserves-prod x y =
      let
        (pair x₊ x₋) = asNatDiff x
        (pair y₊ y₋) = asNatDiff y
        lhs : Int-abs (x * y) ≡ Nat-dist (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊)
        lhs = begin
          Int-abs (x * y)                                              ≡⟨ ap2 (λ e1 e2 → Int-abs (e1 * e2)) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
          Int-abs ((x₊ -ℕ x₋) * (y₊ -ℕ y₋))                            ≡⟨ ap Int-abs (Nat-minus-mul x₊ x₋ y₊ y₋) ⟩
          Int-abs ((x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) -ℕ (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊))   ≡⟨ abs-Nat-minus (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊) ⟩
          Nat-dist (x₊ *ℕ y₊ +ℕ x₋ *ℕ y₋) (x₊ *ℕ y₋ +ℕ x₋ *ℕ y₊)       ∎

        rhs : Int-abs x *ℕ Int-abs y ≡ Nat-dist x₊ x₋ *ℕ Nat-dist y₊ y₋
        rhs = begin
          Int-abs x *ℕ Int-abs y                     ≡⟨ ap2 (λ e1 e2 → Int-abs e1 *ℕ Int-abs e2) (inverse (Nat-minus-asNatDiff x)) (inverse (Nat-minus-asNatDiff y)) ⟩
          Int-abs (x₊ -ℕ x₋) *ℕ Int-abs (y₊ -ℕ y₋)   ≡⟨ ap2 (λ e1 e2 → e1 *ℕ e2) (abs-Nat-minus x₊ x₋) (abs-Nat-minus y₊ y₋) ⟩
          Nat-dist x₊ x₋ *ℕ Nat-dist y₊ y₋           ∎
      in tr2 (λ e1 e2 → e1 ≤ e2) (inverse lhs) (inverse rhs) (Nat-dist.cross-mul-leq-mul x₊ x₋ y₊ y₋)
 