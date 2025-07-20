open import Function.Base using (case_of_)

module _ where
  open import section-10 public

  open Homotopy
  open Homotopy.Symbolic
  open ≡-Basic
  open ≡-Reasoning

  open Equivalence
  open Equivalence.Symbolic

  is-family-of-equivs : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → Set
  is-family-of-equivs {A} f = (x : A) → Is-equiv (f x)

  -- 11.1.1
  totalization : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → Σ A B → Σ A C
  totalization {A} f (x , b) = (x , f x b)

  -- 11.1.2
  fib-tot-pt-eqv-fib-pr1-pr2 : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) →
                               (t : Σ A C) → fib (totalization f) t ≃ fib (f (Σ.fst t)) (Σ.snd t)
  fib-tot-pt-eqv-fib-pr1-pr2 {A} {B} {C} f t =
    (φ t , has-inverse-equiv (ψ t , φψ~id t , ψφ~id t))
    where
      φ : (t' : Σ A C) → fib (totalization f) t' → fib (f (Σ.fst t')) (Σ.snd t')
      φ .(x , f x y) ((x , y) , refl) = (y , refl)
      ψ : (t' : Σ A C) → fib (f (Σ.fst t')) (Σ.snd t') → fib (totalization f) t'
      ψ (x , .(f x y)) (y , refl) = ((x , y) , refl)

      φψ~id : (t' : Σ A C) → φ t' ∘ ψ t' ~ id
      φψ~id (x , .(f x y)) (y , refl) = refl
      ψφ~id : (t' : Σ A C) → ψ t' ∘ φ t' ~ id
      ψφ~id .(x , f x y) (((x , y) , refl)) = refl

  open ↔-Reasoning

  -- 11.1.3
  is-family-of-equivs-iff-tot-is-equiv : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) →
                                         (is-family-of-equivs f ↔ Is-equiv (totalization f))
  is-family-of-equivs-iff-tot-is-equiv {A} {B} {C} f =
    begin-↔
      is-family-of-equivs f                                              ↔⟨⟩
      ((x : A) → Is-equiv (f x))                                         ↔⟨ depfn-iff (λ x → Is-equiv-iff-is-contr-fn) ⟩
      ((x : A) → Is-contr-fn (f x))                                      ↔⟨⟩
      ((x : A) → (c : C x) → Is-contr (fib (f x) c))                     ↔⟨← depfn-iff (λ x → depfn-iff (λ c → equiv-then-contr-iff-contr (fib-tot-pt-eqv-fib-pr1-pr2 f (x , c)))) ⟩
      ((x : A) → (c : C x) → Is-contr (fib (totalization f) (x , c)))    ↔⟨ uncurry-iff ⟩
      ((t : Σ A C) → Is-contr (fib (totalization f) t))                  ↔⟨⟩
      Is-contr-fn (totalization f)                                       ↔⟨← Is-equiv-iff-is-contr-fn ⟩
      Is-equiv (totalization f)                                          ∎-↔

  -- 11.1.4
  module lem-11-1-4 where
    mapleft : {A B : Set} → (f : A → B) → (C : B → Set) → Σ A (λ a → C (f a)) → Σ B C
    mapleft f C (x , c) = (f x , c)

  mapleft-by-equiv-is-equiv : {A B : Set} → {f : A → B} → Is-equiv f → {C : B → Set} → Is-equiv (lem-11-1-4.mapleft f C)
  mapleft-by-equiv-is-equiv {A} {B} {f} f-is-eqv {C} =
    contr-fn-then-equiv (λ t →
      cod-of-equiv-is-contr-then-dom-is-contr
        (has-inverse-equiv (ψ t , G t , H t))
        (Is-equiv-then-is-contr-fn f-is-eqv (Σ.fst t))
    )
    where
      φ : (t : Σ B C) → fib (lem-11-1-4.mapleft f C) t → fib f (Σ.fst t)
      φ .(f x , z) ((x , z) , refl) = (x , refl)
      ψ : (t : Σ B C) → fib f (Σ.fst t) → fib (lem-11-1-4.mapleft f C) t
      ψ (.(f x) , z) (x , refl) = ((x , z) , refl)
      G : (t : Σ B C) → φ t ∘ ψ t ~ id
      G (.(f x) , z) (x , refl) = refl
      H : (t : Σ B C) → ψ t ∘ φ t ~ id
      H .(f x , z) ((x , z) , refl) = refl

  family-of-maps-over : {A B : Set} → (f : A → B) → (C : A → Set) → (D : B → Set) → Set
  family-of-maps-over {A} {B} f C D = (x : A) → C x → D (f x)

  -- 11.1.5
  totalization-over : {A B : Set} → (f : A → B) → {C : A → Set} → (D : B → Set) →
                      family-of-maps-over f C D → Σ A C → Σ B D
  totalization-over f D g (x , z) = (f x , g x z)

  -- 11.1.6
  totalization-of-equivs-over-equiv-is-equiv : {A B : Set} → {f : A → B} → Is-equiv f → {C : A → Set} → {D : B → Set} →
                                               (g : family-of-maps-over f C D) → (is-family-of-equivs g) ↔ Is-equiv (totalization-over f D g)
  totalization-of-equivs-over-equiv-is-equiv {A} {B} {f} f-eqv {C} {D} g =
    begin-↔
      is-family-of-equivs g                                 ↔⟨ is-family-of-equivs-iff-tot-is-equiv g ⟩
      Is-equiv (totalization g)                             ↔⟨← latter-is-equiv-then-comp-is-equiv-iff-former-is-equiv
                                                                  (totalization g)
                                                                  (htpy-refl _)
                                                                  (mapleft-by-equiv-is-equiv f-eqv)
                                                            ⟩
      Is-equiv (lem-11-1-4.mapleft f D ∘ totalization g)    ↔⟨⟩ -- these maps are definitionally equal
      Is-equiv (totalization-over f D g)                    ∎-↔

  -- 11.2.1
  is-identity-system-at : {A : Set} → (a : A) → (B : A → Set) → (b : B a) → Set₁
  is-identity-system-at {A} a B b =
    (P : (x : A) → B x → Set) → Sect (λ (h : (x : A) → (y : B x) → P x y) → h a b)

  identity-system-at : {A : Set} → (a : A) → Set₁
  identity-system-at {A} a =
    Σ-poly (A → Set) (λ B → Σ-poly (B a) (λ b → is-identity-system-at a B b))

  -- 11.2.2
  module fundamental-thm-of-identity-types {A : Set} {a : A} {B : A → Set} where
    -- i-at f is the version assumed in the book, but in fact we can show an even stronger result (ii → i),
    -- because (i) holding at a single function f (i-at f) is actually equivalent to (i) holding at all functions (see i↔i-at-fn for proof)
    i = (f : (x : A) → (a ≡ x) → B x) → is-family-of-equivs f
    ii  = Is-contr (Σ A B)

    iii : (b : B a) → Set₁
    iii b = is-identity-system-at a B b

    i-at : (f : (x : A) → (a ≡ x) → B x) → Set
    i-at f = is-family-of-equivs f

    i-at-fn↔ii : (f : (x : A) → (a ≡ x) → B x) → i-at f ↔ ii
    i-at-fn↔ii f =
      begin-↔
        is-family-of-equivs f                                          ↔⟨ is-family-of-equivs-iff-tot-is-equiv f ⟩
        Is-equiv (totalization f)                                      ↔⟨⟩
        Is-equiv ((totalization f) typed (Σ A (λ x → a ≡ x) → Σ A B))  ↔⟨ dom-is-contr-then-is-equiv-iff-cod-is-contr (identity-with-an-endpoint-fixed-Is-contr a) ⟩
        Is-contr (Σ A B)                                               ∎-↔

    i↔ii : (b : B a) → i ↔ ii
    i↔ii b =
      let
        f₀ : (x : A) → (a ≡ x) → B x
        f₀ = λ x p → tr B p b
      in ((λ i → Σ.fst (i-at-fn↔ii f₀) (i f₀)) , (λ ii f → Σ.snd (i-at-fn↔ii f) ii))

    i↔i-at-fn : (ba : B a) → (f : (x : A) → (a ≡ x) → B x) → i ↔ i-at f
    i↔i-at-fn ba f =
      begin-↔
        i        ↔⟨ i↔ii ba ⟩
        ii       ↔⟨← i-at-fn↔ii f ⟩
        i-at f   ∎-↔

    ii↔iii : (b : B a) → ii ↔-poly (iii b)
    ii↔iii b =
      begin-↔-poly
        Is-contr (Σ A B)                                                     ↔-poly⟨ is-contr-iff-sing-ind-at (a , b) ⟩
        singleton-induction-at (a , b)                                       ↔-poly⟨⟩
        ((P : Σ A B → Set) → Sect (ev-pt (a , b)))                           ↔-poly⟨ curry-type-family ⟩
        ((P : (x : A) → B x → Set) → Sect (ev-pt (a , b)))                   ↔-poly⟨⟩
        ((P : (x : A) → B x → Set) → Sect (ev-at-pair P a b ∘ ev-pair P))    ↔-poly⟨ depfn-iff (λ P →
                                                                              Sect-former-then-Sect-comp-iff-Sect-latter
                                                                                (ev-at-pair P a b)
                                                                                (htpy-refl (ev-at-pair P a b ∘ ev-pair P))
                                                                                (ev-pair-sect P)
                                                                            ) ⟩
        ((P : (x : A) → B x → Set) → Sect (ev-at-pair P a b))                ↔-poly⟨⟩
        is-identity-system-at a B b                                          ∎-↔-poly
      where
        open ↔-poly-Reasoning
        ev-pair : (P : (x : A) → B x → Set) → (((x , y) : Σ A B) → P x y) → (x : A) → (y : B x) → P x y
        ev-pair P h x y = h (x , y)

        ev-at-pair : (P : (x : A) → B x → Set) → (a : A) → (b : B a) → (((x : A) → (y : B x) → P x y) → P a b)
        ev-at-pair P a b f = f a b

        ev-pair-sect : (P : (x : A) → B x → Set) → Sect (ev-pair P)
        ev-pair-sect P = ((λ { f (x , y) → f x y }) , λ f → refl)

    -- the most useful direction of the theorem 11.2.2
    ii→i-at-fn : Is-contr (Σ A B) → (f : (x : A) → (a ≡ x) → B x) → is-family-of-equivs f
    ii→i-at-fn contr@((a' , ba') , C) f = Σ.snd (i-at-fn↔ii f) contr

    ind-≡-family : (b : B a) → (x : A) → (a ≡ x) → B x
    ind-≡-family b x refl = b

    corollary : (b : B a) → is-family-of-equivs (ind-≡-family b) ↔ Is-contr (Σ A B)
    corollary b = i-at-fn↔ii (ind-≡-family b)

  -- subsection 11.3
  module _ where
    open Eq-Nat

    -- 11.3.1
    Eq-Nat-refl-is-equiv : (m n : Nat) → Is-equiv (eq-then-obseq m n)
    Eq-Nat-refl-is-equiv m =
      fundamental-thm-of-identity-types.ii→i-at-fn (contr m) (eq-then-obseq m)
      where
        γ : (m : Nat) → (n : Nat) → (e : Eq-Nat m n) → (m , Eq-Nat-refl m) ≡ (n , e)
        γ zero zero unit = refl
        γ zero (succ n) ()
        γ (succ m) zero ()
        γ (succ m) (succ n) e = -- want : (succ m , Eq-Nat-refl (succ m)) ≡ (succ n , e)
          ap (λ { (n , e) → (succ n , e) })
             (γ m n e)          --      : (m , Eq-Nat-refl m) ≡ (n , e) 
                                -- ... since Eq-Nat-refl (succ m) = Eq-Nat-refl m, this typechecks

        contr : (m : Nat) → Is-contr (Σ Nat (λ n → Eq-Nat m n))
        contr m = ((m , Eq-Nat-refl m) , (λ { (n , e) → γ m n e }))

  -- subsection 11.4
  module _ where
    Is-emb : {A B : Set} → (f : A → B) → Set
    Is-emb {A} {B} f = (x y : A) → Is-equiv (ap f {x} {y})

    _↪_ : Set → Set → Set
    A ↪ B = Σ (A → B) Is-emb

    is-equiv-then-is-emb : {A B : Set} → {e : A → B} → Is-equiv e → Is-emb e
    is-equiv-then-is-emb {A} {B} {e} e-eqv x =
      fundamental-thm-of-identity-types.ii→i-at-fn contr (λ y → ap e {x} {y})
      where
        fib-e-ex-is-contr : Is-contr (fib e (e x))
        fib-e-ex-is-contr = Is-equiv-then-is-contr-fn e-eqv (e x)

        flipped-is-contr : Is-contr (Σ A (λ y → e y ≡ e x))
        flipped-is-contr = fib-e-ex-is-contr -- Σ A (λ y → e y ≡ e x) = fib e (e x)

        contr : Is-contr (Σ A (λ y → e x ≡ e y))
        contr =
          Σ.fst (
            dom-of-equiv-is-contr-iff-cod-is-contr (
               Σ.fst (is-family-of-equivs-iff-tot-is-equiv (λ y e → inverse e))
                (λ y → EqualityOps.inv-is-equiv)
            )
          ) flipped-is-contr

  -- subsection 11.5
  module _ where
    open Equivalence-Reasoning

    open Eq-Copr
    E = Eq-Copr

    -- 11.5.4
    eq-copr-is-contr : {A B : Set} → (s : A +₀ B) → Is-contr (Σ (A +₀ B) (Eq-Copr s))
    eq-copr-is-contr {A} {B} (left x) =
      Σ.snd (equiv-then-contr-iff-contr eqv) (identity-with-an-endpoint-fixed-Is-contr x)
      where
        eqv : Σ (A +₀ B) (E (left x)) ≃ Σ A (λ x' → x ≡ x')
        eqv =
           begin-≃
             Σ (A +₀ B) (E (left x))                                                              ≃⟨ Σ-rdistr-+₀ ⟩
             (Σ A (λ x' → E {A} {B} (left x) (left x'))) +₀ (Σ B (λ y' → E (left x) (right y')))  ≃⟨⟩
             (Σ A (λ x' → x ≡ x')) +₀ (Σ B (λ y' → Empty))                                        ≃⟨ +₀-both-≃ ≃-refl Σ-rzero ⟩     
             (Σ A (λ x' → x ≡ x')) +₀ Empty                                                       ≃⟨ +₀-runit ⟩     
             Σ A (λ x' → x ≡ x')                                                                  ∎-≃
    eq-copr-is-contr {A} {B} (right y) =
      Σ.snd (equiv-then-contr-iff-contr eqv) (identity-with-an-endpoint-fixed-Is-contr y)
      where
        eqv : Σ (A +₀ B) (E (right y)) ≃ (Σ B (λ y' → y ≡ y'))
        eqv =
           begin-≃
             Σ (A +₀ B) (E (right y))                                                               ≃⟨ Σ-rdistr-+₀ ⟩
             (Σ A (λ x' → E (right y) (left x'))) +₀ (Σ B (λ y' → E {A} {B} (right y) (right y')))  ≃⟨⟩
             (Σ A (λ x' → Empty)) +₀ (Σ B (λ y' → y ≡ y'))                                          ≃⟨ +₀-both-≃ Σ-rzero ≃-refl ⟩
             Empty +₀ (Σ B (λ y' → y ≡ y'))                                                         ≃⟨ +₀-lunit ⟩     
             (Σ B (λ y' → y ≡ y'))                                                                    ∎-≃

    -- 11.5.1
    copr-eq-equiv-eq-copr : {A B : Set} → (s t : A +₀ B) → (s ≡ t) ≃ (Eq-Copr s t)
    copr-eq-equiv-eq-copr s t =
      (eq-copr-eq , fundamental-thm-of-identity-types.ii→i-at-fn (eq-copr-is-contr s) (λ ab → eq-copr-eq) t)

    left-left-eq-equiv-eq : {A : Set} → (x x' : A) → (B : Set) →
                            (left {A} {B} x ≡ left x') ≃ (x ≡ x')
    left-left-eq-equiv-eq x x' B = copr-eq-equiv-eq-copr (left x) (left x')

    left-right-eq-equiv-empty : {A B : Set} → (x : A) → (y : B) →
                                (left x ≡ right y) ≃ Empty
    left-right-eq-equiv-empty x y = copr-eq-equiv-eq-copr (left x) (right y)

    right-left-eq-equiv-empty : {A B : Set} → (x : A) → (y : B) →
                                (right y ≡ left x) ≃ Empty
    right-left-eq-equiv-empty {A} {B} x y = copr-eq-equiv-eq-copr (right y) (left x)

    right-right-eq-equiv-eq : (A : Set) → {B : Set} → (y y' : B) →
                             (right {A} {B} y ≡ right y') ≃ (y ≡ y')
    right-right-eq-equiv-eq A {B} y y' = copr-eq-equiv-eq-copr (right y) (right y')

  -- subsection 11.6
  module _ where
    -- 11.6.1
    is-dependent-identity-system-over : {A : Set} → {a : A} → {C : A → Set} → {c : C a} → (is-identity-system-at a C c) → {B : A → Set} → (b : B a) →
                                        (D : (x : A) → B x → C x → Set) → (d : D a b c) → Set₁
    is-dependent-identity-system-over {A} {a} {C} {c} id-sys {B} b D d = is-identity-system-at b (λ y → D a y c) d

    dependent-identity-system-over : {A : Set} → {a : A} → {C : A → Set} → {c : C a} → (is-identity-system-at a C c) → {B : A → Set} → (b : B a) → Set₁
    dependent-identity-system-over {A} {a} {C} {c} id-sys {B} b =
      Σ-poly ((x : A) → B x → C x → Set) (λ D →
        Σ-poly (D a b c) (λ d → is-dependent-identity-system-over id-sys b D d)
      )

    -- 11.6.2 (Structure Identity Principle)
    module SIP {A : Set} {a : A}
               {B : A → Set} (b : B a)
               {C : A → Set} {c : C a} (id-sys : is-identity-system-at a C c)
               (D : (x : A) → B x → C x → Set) where
      open Equivalence-Reasoning

      i   = (f : (y : B a) → (b ≡ y) → D a y c) → is-family-of-equivs f
      ii  = Is-contr (Σ (B a) (λ y → D a y c))

      iii : (d : D a b c) → Set₁
      iii d = is-dependent-identity-system-over id-sys b D d

      iv  = (f : ((x , y) : Σ A B) → ((a , b) ≡ (x , y)) → Σ (C x) (λ z → D x y z)) → is-family-of-equivs f
      v   = Is-contr (Σ (Σ A B) (λ { (x , y) → Σ (C x) (λ z → D x y z) }))

      -- we will fix the point of the identity system to be (c , d), although the book leaves this implicit
      vi : (d : D a b c) → Set₁
      vi d = is-identity-system-at (a , b) (λ { (x , y) → Σ (C x) (λ z → D x y z) }) (c , d)

      i↔ii : (d : D a b c) → i ↔ ii
      i↔ii d = fundamental-thm-of-identity-types.i↔ii d

      ii↔iii : (d : D a b c) → ii ↔-poly (iii d)
      ii↔iii d = fundamental-thm-of-identity-types.ii↔iii d

      iv↔v : (d : D a b c) → iv ↔ v
      iv↔v d = fundamental-thm-of-identity-types.i↔ii (c , d)

      v↔vi : (d : D a b c) → v ↔-poly (vi d)
      v↔vi d = fundamental-thm-of-identity-types.ii↔iii (c , d)

      ii↔v : ii ↔ v
      ii↔v =
        equiv-then-contr-iff-contr (
          ≃-comm (
            begin-≃
              Σ (Σ A B) (λ { (x , y) → Σ (C x) (λ z → D x y z) })
                  ≃⟨ (
                    (λ { ((x , y) , (z , d)) → ((x , z) , (y , d)) }) ,
                    has-inverse-equiv (
                      (λ { ((x , z) , (y , d)) → ((x , y) , (z , d)) }) ,
                      (λ { ((x , y) , (z , d)) → refl }) ,
                      (λ { ((x , z) , (y , d)) → refl })
                    )
                  ) ⟩
              Σ (Σ A C) (λ { (x , z) → Σ (B x) (λ y → D x y z) })
                  ≃⟨
                    Σ-≃-sections-at-base-center (_ ,
                      recenter-contraction-at (a , c) (
                        Σ-poly.snd (fundamental-thm-of-identity-types.ii↔iii c) id-sys))
                  ⟩
              Σ (B a) (λ y → D a y c)   ∎-≃
          )
        )
