open import Function.Base using (case_of_)

module _ where
  open import section-10 public

  open Homotopy
  open Homotopy.Symbolic
  open ≡-Basic
  open ≡-Reasoning

  open Equivalence
  open Equivalence.Symbolic

  Is-family-of-equivs : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → Set
  Is-family-of-equivs {A} f = (x : A) → Is-equiv (f x)

  -- definition 11.1.1
  totalization : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → Σ A B → Σ A C
  totalization {A} f (x , b) = (x , f x b)

  -- lemma 11.1.2
  fib-tot-pt-equiv-fib-pr1-pr2 : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) →
                               (t : Σ A C) → fib (totalization f) t ≃ fib (f (Σ.fst t)) (Σ.snd t)
  fib-tot-pt-equiv-fib-pr1-pr2 {A} {B} {C} f t =
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

  -- theorem 11.1.3
  is-family-of-equivs-iff-tot-is-equiv : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) →
                                         (Is-family-of-equivs f ↔ Is-equiv (totalization f))
  is-family-of-equivs-iff-tot-is-equiv {A} {B} {C} f =
    begin-↔
      Is-family-of-equivs f                                              ↔⟨⟩
      ((x : A) → Is-equiv (f x))                                         ↔⟨ depfn-biimpl (λ x → Is-equiv-iff-is-contr-fn) ⟩
      ((x : A) → Is-contr-fn (f x))                                      ↔⟨⟩
      ((x : A) → (c : C x) → Is-contr (fib (f x) c))                     ↔⟨← depfn-biimpl-2 (λ x c → equiv-then-contr-iff-contr (fib-tot-pt-equiv-fib-pr1-pr2 f (x , c))) ⟩
      ((x : A) → (c : C x) → Is-contr (fib (totalization f) (x , c)))    ↔⟨ uncurry-biimpl ⟩
      ((t : Σ A C) → Is-contr (fib (totalization f) t))                  ↔⟨⟩
      Is-contr-fn (totalization f)                                       ↔⟨← Is-equiv-iff-is-contr-fn ⟩
      Is-equiv (totalization f)                                          ∎-↔

  pointwise-equiv-then-tot-equiv : {A : Set} → {B C : A → Set} → (equivs : (x : A) → B x ≃ C x) → (Σ A B ≃ Σ A C)
  pointwise-equiv-then-tot-equiv {A} {B} {C} equivs =
    let
      equiv-fns : (x : A) → B x → C x
      equiv-fns x = Σ.fst (equivs x)
      equiv-fns-is-family-of-equivs : Is-family-of-equivs equiv-fns
      equiv-fns-is-family-of-equivs x = Σ.snd (equivs x)
    in
      (totalization equiv-fns , Σ.fst (is-family-of-equivs-iff-tot-is-equiv equiv-fns) equiv-fns-is-family-of-equivs)

  leftMap : {A B : Set} → (f : A → B) → (C : B → Set) → Σ A (λ a → C (f a)) → Σ B C
  leftMap f C (x , c) = (f x , c)

  -- lemma 11.1.4
  leftMap-by-equiv-is-equiv : {A B : Set} → {f : A → B} → Is-equiv f → {C : B → Set} → Is-equiv (leftMap f C)
  leftMap-by-equiv-is-equiv {A} {B} {f} f-is-eqv {C} =
    contr-fn-then-equiv (λ t →
      cod-of-equiv-is-contr-then-dom-is-contr
        (has-inverse-equiv (ψ t , G t , H t))
        (Is-equiv-then-is-contr-fn f-is-eqv (Σ.fst t))
    )
    where
      φ : (t : Σ B C) → fib (leftMap f C) t → fib f (Σ.fst t)
      φ .(f x , z) ((x , z) , refl) = (x , refl)
      ψ : (t : Σ B C) → fib f (Σ.fst t) → fib (leftMap f C) t
      ψ (.(f x) , z) (x , refl) = ((x , z) , refl)
      G : (t : Σ B C) → φ t ∘ ψ t ~ id
      G (.(f x) , z) (x , refl) = refl
      H : (t : Σ B C) → ψ t ∘ φ t ~ id
      H .(f x , z) ((x , z) , refl) = refl

  family-of-maps-over : {A B : Set} → (f : A → B) → (C : A → Set) → (D : B → Set) → Set
  family-of-maps-over {A} {B} f C D = (x : A) → C x → D (f x)

  -- definition 11.1.5
  totalizationOver : {A B : Set} → (f : A → B) → {C : A → Set} → (D : B → Set) →
                      family-of-maps-over f C D → Σ A C → Σ B D
  totalizationOver f D g (x , z) = (f x , g x z)

  -- theorem 11.1.6
  totalization-of-equivs-over-equiv-is-equiv : {A B : Set} → {f : A → B} → Is-equiv f → {C : A → Set} → {D : B → Set} →
                                               (g : family-of-maps-over f C D) → (Is-family-of-equivs g) ↔ Is-equiv (totalizationOver f D g)
  totalization-of-equivs-over-equiv-is-equiv {A} {B} {f} f-eqv {C} {D} g =
    begin-↔
      Is-family-of-equivs g                                 ↔⟨ is-family-of-equivs-iff-tot-is-equiv g ⟩
      Is-equiv (totalization g)                             ↔⟨← latter-is-equiv-then-comp-is-equiv-iff-former-is-equiv
                                                                  (totalization g)
                                                                  (htpy-refl _)
                                                                  (leftMap-by-equiv-is-equiv f-eqv)
                                                            ⟩
      Is-equiv (leftMap f D ∘ totalization g)               ↔⟨ homotope-implies-is-equiv-iff (λ { (x , y) → refl }) ⟩
      Is-equiv (totalizationOver f D g)                    ∎-↔

  -- definition 11.2.1
  Is-identity-system-at : {A : Set} → (a : A) → (B : A → Set) → (b : B a) → Set₁
  Is-identity-system-at {A} a B b =
    (P : Σ A B → Set) → Sect (λ (h : (x : A) → (y : B x) → P (x , y)) → h a b)

  identity-system-at : {A : Set} → (a : A) → Set₁
  identity-system-at {A} a =
    Σ-poly (A → Set) (λ B → Σ-poly (B a) (λ b → Is-identity-system-at a B b))

  -- theorem 11.2.2
  module fundamental-thm-of-identity-types {A : Set} {a : A} {B : A → Set} where
    -- i-at f is the version assumed in the book, but in fact we can show an even stronger result (ii → i),
    -- because (i) holding at a single function f (i-at f) is actually equivalent to (i) holding at all functions (see i↔i-at-fn for proof)
    i = (f : (x : A) → (a ≡ x) → B x) → Is-family-of-equivs f
    ii  = Is-contr (Σ A B)

    iii : (b : B a) → Set₁
    iii b = Is-identity-system-at a B b

    i-at : (f : (x : A) → (a ≡ x) → B x) → Set
    i-at f = Is-family-of-equivs f

    i-at-fn↔ii : (f : (x : A) → (a ≡ x) → B x) → i-at f ↔ ii
    i-at-fn↔ii f =
      begin-↔
        Is-family-of-equivs f                                          ↔⟨ is-family-of-equivs-iff-tot-is-equiv f ⟩
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
        Is-contr (Σ A B)                                          ↔-poly⟨ is-contr-iff-sing-ind-at (a , b) ⟩
        singleton-induction-at (a , b)                            ↔-poly⟨⟩
        ((P : Σ A B → Set) → Sect (ev-pt {Σ A B} {P} (a , b)))    ↔-poly⟨⟩
        ((P : Σ A B → Set) → Sect (ev-at-pair P a b ∘ ev-pair P)) ↔-poly⟨ depfn-biimpl (λ P →
                                                                    Sect-former-then-Sect-comp-biimpl-Sect-latter
                                                                      (ev-at-pair P a b)
                                                                      (htpy-refl (ev-at-pair P a b ∘ ev-pair P))
                                                                      (ev-pair-sect P)
                                                                  ) ⟩
        ((P : Σ A B → Set) → Sect (ev-at-pair P a b))             ↔-poly⟨⟩
        Is-identity-system-at a B b                               ∎-↔-poly
      where
        open ↔-poly-Reasoning
        ev-pair : (P : Σ A B → Set) → ((t : Σ A B) → P t) → (x : A) → (y : B x) → P (x , y)
        ev-pair P h x y = h (x , y)

        ev-at-pair : (P : Σ A B → Set) → (a : A) → (b : B a) → (((x : A) → (y : B x) → P (x , y)) → P (a , b))
        ev-at-pair P a b f = f a b

        ev-pair-sect : (P : Σ A B → Set) → Sect (ev-pair P)
        ev-pair-sect P = (ind-Σ , λ { h → refl })

    -- the most useful direction of the theorem 11.2.2
    ii→i-at-fn : Is-contr (Σ A B) → (f : (x : A) → (a ≡ x) → B x) → Is-family-of-equivs f
    ii→i-at-fn contr@((a' , ba') , C) f = Σ.snd (i-at-fn↔ii f) contr

    is-contr-then-has-identity-system-at-any-pt : Is-contr (Σ A B) → (b : B a) → Is-identity-system-at a B b
    is-contr-then-has-identity-system-at-any-pt contr b = Σ-poly.fst (ii↔iii b) contr

    ind-≡-family : (b : B a) → (x : A) → (a ≡ x) → B x
    ind-≡-family b x refl = b

    corollary : (b : B a) → Is-family-of-equivs (ind-≡-family b) ↔ Is-contr (Σ A B)
    corollary b = i-at-fn↔ii (ind-≡-family b)

  -- subsection 11.3
  module _ where
    open Eq-Nat

    -- theorem 11.3.1
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
    -- definition 11.4.1
    Is-emb : {A B : Set} → (f : A → B) → Set
    Is-emb {A} {B} f = (x y : A) → Is-equiv (ap f {x} {y})

    _↪_ : Set → Set → Set
    A ↪ B = Σ (A → B) Is-emb

    -- theorem 11.4.2
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

    -- proposition 11.5.4
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
             (Σ B (λ y' → y ≡ y'))                                                                  ∎-≃

    -- theorem 11.5.1
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
    -- definition 11.6.1
    Is-dependent-identity-system-over : {A : Set} → {a : A} → {C : A → Set} → {c : C a} → (Is-identity-system-at a C c) → {B : A → Set} → (b : B a) →
                                        (D : (x : A) → B x → C x → Set) → (d : D a b c) → Set₁
    Is-dependent-identity-system-over {A} {a} {C} {c} id-sys {B} b D d = Is-identity-system-at b (λ y → D a y c) d

    dependent-identity-system-over : {A : Set} → {a : A} → {C : A → Set} → {c : C a} → (Is-identity-system-at a C c) → {B : A → Set} → (b : B a) → Set₁
    dependent-identity-system-over {A} {a} {C} {c} id-sys {B} b =
      Σ-poly ((x : A) → B x → C x → Set) (λ D →
        Σ-poly (D a b c) (λ d → Is-dependent-identity-system-over id-sys b D d)
      )

    -- theorem 11.6.2 (Structure Identity Principle)
    module SIP {A : Set} {a : A}
               (B : A → Set) (b : B a)
               (C : A → Set) {c : C a} (id-sys : Is-identity-system-at a C c)
               (D : (x : A) → B x → C x → Set) where
      open Equivalence-Reasoning

      i   = (f : (y : B a) → (b ≡ y) → D a y c) → Is-family-of-equivs f
      ii  = Is-contr (Σ (B a) (λ y → D a y c))

      iii : (d : D a b c) → Set₁
      iii d = Is-dependent-identity-system-over id-sys b D d

      iv  = (f : (xy@(x , y) : Σ A B) → ((a , b) ≡ xy) → Σ (C x) (λ z → D x y z)) → Is-family-of-equivs f
      v   = Is-contr (Σ (Σ A B) (λ (x , y) → Σ (C x) (λ z → D x y z)))

      -- we will fix the point of the identity system to be (c , d), although the book leaves this implicit
      vi : (d : D a b c) → Set₁
      vi d = Is-identity-system-at (a , b) (λ (x , y) → Σ (C x) (λ z → D x y z)) (c , d)

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
          begin-≃
            Σ (B a) (λ y → D a y c)
              ≃⟨←
                Σ-≃-sections-at-base-center (_ ,
                  recenter-contraction-at (a , c) (
                    Σ-poly.snd (fundamental-thm-of-identity-types.ii↔iii c) id-sys))
              ⟩
            Σ (Σ A C) (λ xz → Σ (B (Σ-poly.fst xz)) (λ y → D (Σ-poly.fst xz) y (Σ-poly.snd xz)))
              ≃⟨← (
                (λ { ((x , y) , (z , d)) → ((x , z) , (y , d)) }) ,
                has-inverse-equiv (
                  (λ { ((x , z) , (y , d)) → ((x , y) , (z , d)) }) ,
                  (λ { ((x , y) , (z , d)) → refl }) ,
                  (λ { ((x , z) , (y , d)) → refl })
                )
              ) ⟩
            Σ (Σ A B) (λ xy → Σ (C (Σ-poly.fst xy)) (λ z → D (Σ-poly.fst xy) (Σ-poly.snd xy) z))  ∎-≃
        )

      ii→iv : (d : D a b c) → ii → iv
      ii→iv d = (Σ.snd (iv↔v d)) ∘ (Σ.fst ii↔v)

    -- example 11.6.3
    fib-eq-≃-fib-apf-concat : {A B : Set} → (f : A → B) → (b : B) →
                              ((x , p) (y , q) : fib f b) → ((x , p) ≡ (y , q)) ≃ fib (ap f) (p · q ⁻¹)
    fib-eq-≃-fib-apf-concat {A} {B} f b (x , p) =
      (λ { (y , q) → (_ , eqvs-is-family-of-equivs (y , q)) })
      where
        eqvs : (yq@(y , q) : fib f b) → ((x , p) ≡ yq) → Σ (x ≡ y) (λ α → ap f α ≡ p · q ⁻¹)
        eqvs yq refl = (refl , (inverse (≡-Basic.·-rinv p)))

        equivalence : Σ (f x ≡ b) (λ q → ap f refl ≡ p · q ⁻¹) ≃ Σ (f x ≡ b) (λ q → p ≡ q)
        equivalence =
          let
            forward : (q : f x ≡ b) → refl ≡ p · q ⁻¹ → p ≡ q
            forward = λ { refl α → (α · (·-runit p))⁻¹ }
            backward : (q : f x ≡ b) → p ≡ q → refl ≡ p · q ⁻¹
            backward = λ { refl α → ((·-runit p) · α) ⁻¹ }
          in (_ ,
            Σ.fst (is-family-of-equivs-iff-tot-is-equiv forward) (λ { refl →
              has-inverse-equiv (
                backward refl ,
                (λ { refl → refl }) ,
                (λ r → begin
                  (backward refl ∘ (λ z → forward refl z)) r      ≡⟨⟩
                  backward refl (forward refl r)                  ≡⟨⟩
                  ((·-runit p) · (forward refl r))⁻¹              ≡⟨⟩
                  ((·-runit p) · (r · (·-runit p))⁻¹)⁻¹           ≡⟨ ap (λ s → ((·-runit p) · s)⁻¹) (≡-Basic1.distr-inv-concat r (·-runit p)) ⟩
                  ((·-runit p) · ((·-runit p)⁻¹ · r ⁻¹))⁻¹        ≡⟨ ap (λ s → s ⁻¹) (·-unassoc (·-runit p) _ _) ⟩
                  ((·-runit p) · (·-runit p)⁻¹ · r ⁻¹)⁻¹          ≡⟨ ap (λ s → (s · r ⁻¹)⁻¹) (·-rinv (·-runit p)) ⟩
                  (refl · r ⁻¹)⁻¹                                 ≡⟨⟩
                  (r ⁻¹)⁻¹                                        ≡⟨ ≡-Basic1.inv-inv r ⟩
                  r                                               ∎
                )
              )
            } )
          )

        eqvs-is-family-of-equivs =
          SIP.ii→iv
            (λ (y : A) → f y ≡ b) p
            (λ (y : A) → x ≡ y) (fundamental-thm-of-identity-types.is-contr-then-has-identity-system-at-any-pt (identity-with-an-endpoint-fixed-Is-contr x) refl)
            (λ (y : A) (q : f y ≡ b) (α : x ≡ y) → ap f α ≡ p · q ⁻¹) (inverse (≡-Basic.·-rinv p))
            (Σ.snd (equiv-then-contr-iff-contr equivalence) (identity-with-an-endpoint-fixed-Is-contr _))
            eqvs

  -- exercise 11.1
  module _ where
    -- exercise 11.1.a
    empty-map-is-emb : {A : Set} → (f : Empty → A) → Is-emb f
    empty-map-is-emb {A} f ()

    -- exercise 11.1.b
    left-is-emb : (A B : Set) → Is-emb (left {A} {B})
    left-is-emb A B x y =
      let
        equiv : Σ A (λ z → left x ≡ left z) ≃ Σ A (λ z → x ≡ z)
        equiv = pointwise-equiv-then-tot-equiv (λ z → left-left-eq-equiv-eq x z B)
        contr : Is-contr (Σ A (λ z → left x ≡ left z))
        contr = Σ.snd (equiv-then-contr-iff-contr equiv) (identity-with-an-endpoint-fixed-Is-contr x)
      in fundamental-thm-of-identity-types.ii→i-at-fn contr (λ _ → ap (left {A} {B})) y

    right-is-emb : (A B : Set) → Is-emb (right {A} {B})
    right-is-emb A B x y =
      let
        equiv : Σ B (λ z → right x ≡ right z) ≃ Σ B (λ z → x ≡ z)
        equiv = pointwise-equiv-then-tot-equiv (λ z → right-right-eq-equiv-eq A x z)
        contr : Is-contr (Σ B (λ z → right x ≡ right z))
        contr = Σ.snd (equiv-then-contr-iff-contr equiv) (identity-with-an-endpoint-fixed-Is-contr x)
      in fundamental-thm-of-identity-types.ii→i-at-fn contr (λ _ → ap (right {A} {B})) y

    open EmptyBasic

    -- exercise 11.1.c
    left-is-equiv-iff-right-type-is-empty : (A B : Set) → Is-equiv (left {A} {B}) ↔ Is-empty B
    left-is-equiv-iff-right-type-is-empty A B =
      (
        (λ { ((s , S) , _) b → Eq-Copr.left-neq-right (S (right b)) }) ,
        (λ ¬B → has-inverse-equiv (
          (λ { (left a) → a    ; (right b) → absurd (¬B b) }) ,
          (λ { (left a) → refl ; (right b) → absurd (¬B b) }) ,
          (λ a → refl)
        ))
      )

    right-is-equiv-iff-left-type-is-empty : (A B : Set) → Is-equiv (right {A} {B}) ↔ Is-empty A
    right-is-equiv-iff-left-type-is-empty A B =
      (
        (λ { ((s , S) , _) a → Eq-Copr.right-neq-left (S (left a)) }) ,
        (λ ¬A → has-inverse-equiv (
          (λ { (left a) → absurd (¬A a) ; (right b) → b }) ,
          (λ { (left a) → absurd (¬A a) ; (right b) → refl }) ,
          (λ b → refl)
        ))
      )

  -- exercise 11.2
  module _ where
    equivalence-ladjoint : {A B : Set} → ((e , e-eqv) : A ≃ B) → (x : A) → (y : B) →
                           let e⁻¹ = ≃-inverse-map-for e-eqv in (e x ≡ y) ≃ (x ≡ e⁻¹ y)
    equivalence-ladjoint {A} {B} (e , e-eqv) x y =
      let
        e⁻¹               = ≃-inverse-map-for e-eqv
        (S , R)           = ≃-inverse-map-is-inverse-of-original e-eqv
        (R' , R'e⁻¹~e⁻¹S) = improve-section-of-inverse-to-be-coherent e⁻¹ (e , R , S)
        Se~eR'            = Is-coh-invertible-then-inverse-is-coh-invertible e⁻¹ e R' S R'e⁻¹~e⁻¹S

        forward : (e x ≡ y) → (x ≡ e⁻¹ y)
        forward p = (R' x)⁻¹ · (ap e⁻¹ p)

        backward : (x ≡ e⁻¹ y) → (e x ≡ y)
        backward p = (ap e p) · (S y)
      in
        (
          forward ,
          has-inverse-equiv (
            backward ,
            (λ { refl → begin
              (forward ∘ backward) refl                         ≡⟨⟩
              (R' x)⁻¹ · (ap e⁻¹ ((ap e refl) · (S y)))         ≡⟨⟩
              (R' x)⁻¹ · (ap e⁻¹ (refl · (S y)))                ≡⟨⟩
              (R' x)⁻¹ · (ap e⁻¹ (S y))                         ≡⟨⟩ -- x = e⁻¹ y thanks to path-induction
              (R' (e⁻¹ y))⁻¹ · (ap e⁻¹ (S y))                   ≡⟨ ≡-Basic1.inv-con-eq-refl (inverse (R'e⁻¹~e⁻¹S y)) ⟩
              refl                                              ∎
            }) ,
            (λ { refl → begin
              (backward ∘ forward) refl                  ≡⟨⟩
              backward ((R' x)⁻¹ · (ap e⁻¹ refl))        ≡⟨⟩
              backward ((R' x)⁻¹ · refl)                 ≡⟨ ap backward (·-runit ((R' x)⁻¹)) ⟩
              backward ((R' x)⁻¹)                        ≡⟨⟩
              (ap e ((R' x)⁻¹)) · (S y)                  ≡⟨⟩ -- y = e x thanks to path-induction
              (ap e ((R' x)⁻¹)) · (S (e x))              ≡⟨ ap (λ s → s · (S (e x))) (ap-inv e (R' x)) ⟩
              (ap e (R' x))⁻¹ · (S (e x))                ≡⟨ ≡-Basic1.inv-con-eq-refl (Se~eR' x) ⟩
              refl                                       ∎
            })
          )
        )

    equivalence-ladjoint-counit-universality : {A B : Set} → ((e , e-eqv) : A ≃ B) → (x : A) → (y : B) →
                                               let e⁻¹               = ≃-inverse-map-for e-eqv
                                                   (S , R)           = ≃-inverse-map-is-inverse-of-original e-eqv
                                                   (ladj , ladj-eqv) = equivalence-ladjoint (e , e-eqv) x y
                                               in (p : e x ≡ y) → ((ap e (ladj p)) · (S y) ≡ p)
    equivalence-ladjoint-counit-universality {A} {B} (e , e-eqv) x y refl =
      let (ladj , (Sect , (_ , ladj-Retr))) = equivalence-ladjoint (e , e-eqv) x y
      in
        -- if you look closely, you will see that
        --   (equivalence-ladjoint.backward ∘ equivalence-ladjoint.forward) refl ≡ refl
        -- is exactly what we want, and that is already proven in the definition of equivalence-ladjoint.
        ladj-Retr refl

    open Homotopy.HomotopyGroupoidSymbolic
    equivalence-ladjoint-unit-universality : {A B : Set} → ((e , e-eqv) : A ≃ B) → (x : A) → (y : B) →
                                             let e⁻¹               = ≃-inverse-map-for e-eqv
                                                 (S , R)           = ≃-inverse-map-is-inverse-of-original e-eqv
                                                 (R' , R'e⁻¹~e⁻¹S) = improve-section-of-inverse-to-be-coherent e⁻¹ (e , R , S)
                                                 (ladj , ((ladj⁻¹ , ladjS) , _)) = equivalence-ladjoint (e , e-eqv) x y
                                             -- NOTE: This side of the universality is stated in terms of the improved homotopy R'
                                             --       instead of the original homotopy R. This is because the universality statement
                                             --       exactly corresponds to the property of S and R of being a part of the is-coh-inv structure,
                                             --       and since (e , e-eqv) does not necessarily come with a coherent inverse,
                                             --       we had to make a choice in equivalence-ladjoint about which of retract and section
                                             --       we must promote to become part of the is-coh-inv structure.
                                             --       Had we stated the type equivalence (A ≃ B) in terms of is-coh-inv structure,
                                             --       this asymmetry would vanish, and we should be able to write down and prove
                                             --       the universality with the original homotopies that came along with (A ≃ B).
                                             in (q : x ≡ e⁻¹ y) → (((R' ⁻¹ₕₜₚ)  x) · (ap e⁻¹ (ladj⁻¹ q)) ≡ q)
    equivalence-ladjoint-unit-universality {A} {B} (e , e-eqv) x y refl =
      let (ladj , ((_ , ladj-Sect) , Retr)) = equivalence-ladjoint (e , e-eqv) x y
      in
        -- if you look closely, you will see that
        --   (equivalence-ladjoint.forward ∘ equivalence-ladjoint.backward) refl ≡ refl
        -- is exactly what we want, and that is already proven in the definition of equivalence-ladjoint.
        ladj-Sect refl

  -- exercise 11.3
  module _ where
    homotope-ap : {A B : Set} → (f g : A → B) → (H : f ~ g) → {x y : A} → (x ≡ y) → (f x ≡ f y)
    homotope-ap {A} {B} f g H {x} {y} p = H x · ap g p · ((H y) ⁻¹)

    homotope-ap-refl-eq-refl : {A B : Set} → {f g : A → B} → (H : f ~ g) → {x : A} → homotope-ap f g H {x} {x} refl ≡ refl
    homotope-ap-refl-eq-refl {A} {B} {f} {g} H {x} =
      begin
        homotope-ap f g H {x} {x} refl   ≡⟨⟩
        H x · ap g refl · ((H x) ⁻¹)     ≡⟨⟩
        H x · refl · ((H x) ⁻¹)          ≡⟨ ·-assoc (H x) _ _ ⟩
        H x · (refl · ((H x) ⁻¹))        ≡⟨⟩
        H x · ((H x) ⁻¹)                 ≡⟨ ·-rinv (H x) ⟩
        refl                             ∎

    homotope-ap-homotopy : {A B : Set} → {f g : A → B} → (x y : A) → (H : f ~ g) → (ap f {x} {y}) ~ (homotope-ap f g H)
    homotope-ap-homotopy {A} {B} {f} {g} x y H refl =
      begin
        ap f refl                ≡⟨⟩
        refl                     ≡⟨← homotope-ap-refl-eq-refl H ⟩
        homotope-ap f g H refl   ∎

    -- We will show: Is-equiv (ap f) ⇒ Is-equiv (homotope-ap f g H) ⇒ Is-equiv (ap g).
    -- The middle type is Is-equiv (λ p → H x · ap g p · ((H y) ⁻¹)),
    -- so we'll prove two lemmas to "unwrap" surrounding equalities (H x and (H y) ⁻¹).

    is-emb-then-homotope-ap-is-equiv : {A B : Set} → {f g : A → B} → (H : f ~ g) → Is-emb f → (x y : A) → Is-equiv (homotope-ap f g H {x} {y})
    is-emb-then-homotope-ap-is-equiv {A} {B} {f} {g} H f-emb x y =
      is-equiv-preserved-by-homotopy
        (homotope-ap-homotopy x y H)
        (f-emb x y)

    is-equiv-preserved-by-·-left : {A B : Set} → {x y : A} → {x' y' : B} →
                                   {path-fn : x ≡ y → x' ≡ y'} → {z : B} → (p : z ≡ x') →
                                   Is-equiv path-fn → Is-equiv (λ q → p · path-fn q)
    is-equiv-preserved-by-·-left {A} {B} {x} {y} {f} {path-fn} {z} refl path-fn-eqv = path-fn-eqv

    is-equiv-preserved-by-·-right : {A B : Set} → {x y : A} → {x' y' : B} →
                                    {path-fn : x ≡ y → x' ≡ y'} → {z : B} → (p : y' ≡ z) →
                                    Is-equiv path-fn → Is-equiv (λ q → path-fn q · p)
    is-equiv-preserved-by-·-right {A} {B} {x} {y} {f} {g} {path-fn} {z} refl ((s , S) , (r , R)) =
      (
        (s , λ x'≡y' → begin
          ((λ q → path-fn q · refl) ∘ s) x'≡y'     ≡⟨⟩
          path-fn (s x'≡y') · refl                 ≡⟨ ·-runit _ ⟩
          path-fn (s x'≡y')                        ≡⟨ S _ ⟩
          x'≡y'                                    ∎
        ),
        (r , λ x'≡y' → begin
          (r ∘ (λ q → path-fn q · refl)) x'≡y'     ≡⟨⟩
          r (path-fn x'≡y' · refl)                 ≡⟨ ap r (·-runit _) ⟩
          r (path-fn x'≡y')                        ≡⟨ R _ ⟩
          x'≡y'                                    ∎
        )
      )

    homotope-ap-is-equiv-then-ap-target-is-equiv : {A B : Set} → {f g : A → B} → (x y : A) → (H : f ~ g) →
                                                   Is-equiv (homotope-ap f g H {x} {y}) → Is-equiv (ap g {x} {y})
    homotope-ap-is-equiv-then-ap-target-is-equiv {A} {B} {f} {g} x y H is-equiv-homotope-ap =
      let
        is-equiv-Hx⁻¹·Hx·apg·Hy⁻¹·Hy : Is-equiv (λ p → ((H x) ⁻¹) · (H x · ap g p · ((H y) ⁻¹) · H y))
        is-equiv-Hx⁻¹·Hx·apg·Hy⁻¹·Hy =
          is-equiv-preserved-by-·-left ((H x) ⁻¹) (
            is-equiv-preserved-by-·-right (H y) is-equiv-homotope-ap
          )

        Hx⁻¹·Hx·apg·Hy⁻¹·Hy~apg : (λ p → ((H x) ⁻¹) · (H x · ap g p · ((H y) ⁻¹) · H y)) ~ ap g
        Hx⁻¹·Hx·apg·Hy⁻¹·Hy~apg =
          (λ { refl → begin
            H x ⁻¹ · (H x · ap g refl · H y ⁻¹ · H y)   ≡⟨⟩
            H x ⁻¹ · (H x · refl · H y ⁻¹ · H y)        ≡⟨ ap (λ c → H x ⁻¹ · (c · H y ⁻¹ · H y)) (·-runit _) ⟩
            H x ⁻¹ · (H x · H y ⁻¹ · H y)               ≡⟨ ap (λ c → H x ⁻¹ · c) (·-assoc (H x) _ _) ⟩
            H x ⁻¹ · (H x · (H y ⁻¹ · H y))             ≡⟨ ap (λ c → H x ⁻¹ · (H x · c)) (·-linv (H y)) ⟩
            H x ⁻¹ · (H x · refl)                       ≡⟨ ap (λ c → H x ⁻¹ · c) (·-runit _) ⟩
            H x ⁻¹ · H x                                ≡⟨ ·-linv (H x) ⟩
            refl                                        ≡⟨⟩
            ap g refl                                   ∎
          })
      in is-equiv-preserved-by-homotopy Hx⁻¹·Hx·apg·Hy⁻¹·Hy~apg is-equiv-Hx⁻¹·Hx·apg·Hy⁻¹·Hy

    is-emb-preserved-by-homotopy : {A B : Set} → {f g : A → B} → (H : f ~ g) → (Is-emb f → Is-emb g)
    is-emb-preserved-by-homotopy {A} {B} {f} {g} H f-emb x y =
      homotope-ap-is-equiv-then-ap-target-is-equiv x y H
        (is-emb-then-homotope-ap-is-equiv H f-emb x y)

    open Homotopy.HomotopyGroupoidSymbolic
    homotope-ap-is-equiv-then-homotope-ap-inv-is-equiv : {A B : Set} → {f g : A → B} → (H : f ~ g) → {x y : A} →
                                                        Is-equiv (homotope-ap f g H {x} {y}) →
                                                        Is-equiv (homotope-ap g f (H ⁻¹ₕₜₚ) {x} {y})
    homotope-ap-is-equiv-then-homotope-ap-inv-is-equiv {A} {B} {f} {g} H {x} {y} is-equiv-homotope-ap =
      let
        ap-g-is-eqv : Is-equiv (ap g {x} {y})
        ap-g-is-eqv = homotope-ap-is-equiv-then-ap-target-is-equiv x y H is-equiv-homotope-ap

        ap-g~homotope-ap-Hinv : ap g {x} {y} ~ homotope-ap g f (H ⁻¹ₕₜₚ)
        ap-g~homotope-ap-Hinv = homotope-ap-homotopy x y (H ⁻¹ₕₜₚ)
      in is-equiv-preserved-by-homotopy ap-g~homotope-ap-Hinv ap-g-is-eqv

  -- exercise 11.4
  module _ where
    open Homotopy.HomotopyGroupoidSymbolic

    comp-embs-is-emb : {A B C : Set} → {g : B → C} → {f : A → B} → Is-emb g → Is-emb f → Is-emb (g ∘ f)
    comp-embs-is-emb {A} {B} {C} {g} {f} g-emb f-emb x y =
      is-equiv-preserved-by-homotopy (λ { refl → refl }) (comp-equivs-is-equiv (g-emb (f x) (f y)) (f-emb x y))

    -- exercise 11.4.a
    latter-is-emb-then-comp-is-emb-iff-former-is-emb : {A B X : Set} → (h : A → B) → {g : B → X} → {f : A → X} →
                                                        (H : f ~ g ∘ h) → (Is-emb g) → (Is-emb f ↔ Is-emb h)
    latter-is-emb-then-comp-is-emb-iff-former-is-emb {A} {B} {X} h {g} {f} H g-emb =
      (
        (λ f-emb x y →
          let
            (apg⁻¹ , apg⁻¹-S , apg⁻¹-R) = equiv-has-inverse (g-emb (h x) (h y))

            -- We expect, morally, that apg⁻¹ ∘ ap f ~ ap h and that the LHS to be an equivalence.
            -- The issue is that the LHS in the expression above is ill-typed, so we instead assert:
            homotopy : apg⁻¹ ∘ (homotope-ap (g ∘ h) f (H ⁻¹ₕₜₚ)) ~ ap h
            homotopy =
              (λ { refl → begin
                (apg⁻¹ ∘ (homotope-ap (g ∘ h) f (H ⁻¹ₕₜₚ))) refl   ≡⟨⟩
                apg⁻¹ (homotope-ap (g ∘ h) f (H ⁻¹ₕₜₚ) refl)       ≡⟨ ap apg⁻¹ (homotope-ap-refl-eq-refl (H ⁻¹ₕₜₚ)) ⟩
                apg⁻¹ refl                                         ≡⟨⟩
                apg⁻¹ (ap g refl)                                  ≡⟨ apg⁻¹-R refl ⟩
                refl                                               ∎
              })
            apg⁻¹-is-eqv = has-inverse-equiv (ap g , apg⁻¹-R , apg⁻¹-S)
            homotope-ap-H⁻¹-is-eqv =
              homotope-ap-is-equiv-then-homotope-ap-inv-is-equiv H (
                is-emb-then-homotope-ap-is-equiv H f-emb x y
              )
          in is-equiv-preserved-by-homotopy homotopy (comp-equivs-is-equiv apg⁻¹-is-eqv homotope-ap-H⁻¹-is-eqv)
        ) ,
        (λ h-emb → is-emb-preserved-by-homotopy (H ⁻¹ₕₜₚ) (comp-embs-is-emb g-emb h-emb))
      )

    latter-and-comp-are-embs-then-comp-is-emb-iff-former-is-emb : {A B X : Set} → (h : A → B) → {g : B → X} → {f : A → X} →
                                                                  (H : f ~ g ∘ h) → Is-emb g → Is-emb f → Is-emb h
    latter-and-comp-are-embs-then-comp-is-emb-iff-former-is-emb {A} {B} {X} h {g} {f} H g-emb f-emb =
      Σ.fst (latter-is-emb-then-comp-is-emb-iff-former-is-emb h H g-emb) f-emb

    -- exercise 11.4.b
    former-is-equiv-then-comp-is-emb-iff-latter-is-emb : {A B X : Set} → (h : A → B) → {g : B → X} → {f : A → X} →
                                                       (H : f ~ g ∘ h) → Is-equiv h → (Is-emb g ↔ Is-emb f)
    former-is-equiv-then-comp-is-emb-iff-latter-is-emb {A} {B} {X} h {g} {f} H h-eqv =
      let
        h⁻¹ = ≃-inverse-map-for h-eqv
        f∘h⁻¹~g : f ∘ h⁻¹ ~ g
        f∘h⁻¹~g b =
          begin
            (f ∘ h⁻¹) b    ≡⟨⟩
            f (h⁻¹ b)      ≡⟨ H (h⁻¹ b) ⟩
            g (h (h⁻¹ b))  ≡⟨ ap g (≃-inverse-map-is-sect-of-original h-eqv b) ⟩
            g b            ∎
      in
        (
          (λ g-emb → is-emb-preserved-by-homotopy (H ⁻¹ₕₜₚ) (comp-embs-is-emb g-emb (is-equiv-then-is-emb h-eqv))) ,
          (λ f-emb → is-emb-preserved-by-homotopy (f∘h⁻¹~g) (comp-embs-is-emb f-emb (is-equiv-then-is-emb (≃-inverse-map-is-equiv h-eqv))))
        )

  -- exercise 11.5
  module _ where
    sect-comp-to-sect-latter : {A B C : Set} → (g : B → C) → (f : A → B) →
                               Sect (g ∘ f) → Sect g
    sect-comp-to-sect-latter {A} {B} {C} g f (s , S) = (f ∘ s , S)

    retr-comp-to-retr-former : {A B C : Set} → (g : B → C) → (f : A → B) →
                               Retr (g ∘ f) → Retr f
    retr-comp-to-retr-former {A} {B} {C} g f (r , R) = (r ∘ g , R)

    sect-comp-and-latter-is-emb-to-retr-latter : {A B C : Set} → (g : B → C) → (f : A → B) →
                                                 Sect (g ∘ f) → Is-emb g → Retr g
    sect-comp-and-latter-is-emb-to-retr-latter {A} {B} {C} g f (s , S) g-emb =
      (f ∘ s , λ b → ≃-inverse-map-for (g-emb ((f ∘ s ∘ g) b) b) (S (g b)))

    sect-comp-and-latter-is-emb-to-sect-former : {A B C : Set} → (g : B → C) → (f : A → B) →
                                                 Sect (g ∘ f) → Is-emb g → Sect f
    sect-comp-and-latter-is-emb-to-sect-former {A} {B} {C} g f (s , S) g-emb =
      (s ∘ g , λ b → ≃-inverse-map-for (g-emb ((f ∘ s ∘ g) b) b) (S (g b)))

    -- exercise 11.5 (i) → (ii) (we show a stronger statement that does not require (Is-emb f))
    latter-is-emb-and-comp-is-equiv-then-both-are-equiv : {A B C : Set} → {g : B → C} → {f : A → B} →
                                                          Is-emb g → Is-equiv (g ∘ f) → Is-equiv g × Is-equiv f
    latter-is-emb-and-comp-is-equiv-then-both-are-equiv {A} {B} {C} {g} {f} g-emb (sect , retr) =
      (
        (sect-comp-to-sect-latter g f sect , sect-comp-and-latter-is-emb-to-retr-latter g f sect g-emb) ,
        (sect-comp-and-latter-is-emb-to-sect-former g f sect g-emb , retr-comp-to-retr-former g f retr)
      )

    -- exercise 11.5 (ii) → (i)
    both-embs-are-equivs-then-comp-is-equiv : {A B C : Set} → {g : B → C} → {f : A → B} →
                                              Is-emb g → Is-emb f → Is-equiv g → Is-equiv f →
                                              Is-equiv (g ∘ f)
    both-embs-are-equivs-then-comp-is-equiv {A} {B} {C} {g} {f} _ _ g-eqv f-eqv =
      comp-equivs-is-equiv g-eqv f-eqv

  -- exercise 11.6
  module _ where
    open +₀-Basic
    open EmptyBasic

    +₀-univ-map-is-emb-then-both-are-emb-and-neq : {A B C : Set} → {f : A → C} → {g : B → C} →
                                                   Is-emb ([ f +₀ g ]) → Is-emb f × Is-emb g × ((a : A) → (b : B) → ¬ (f a ≡ g b))
    +₀-univ-map-is-emb-then-both-are-emb-and-neq {A} {B} {C} {f} {g} f+g-emb =
      (
        (λ a a' →
          is-equiv-preserved-by-homotopy
            (λ { refl → refl })
            (comp-equivs-is-equiv (f+g-emb (left a) (left a')) (left-is-emb A B a a'))),
        (λ b b' →
          is-equiv-preserved-by-homotopy
            (λ { refl → refl })
            (comp-equivs-is-equiv (f+g-emb (right b) (right b')) (right-is-emb A B b b'))),
        (λ a b fa≡gb →
          let
            [f+₀g]la≡[f+₀g]rb : [ f +₀ g ] (left a) ≡ [ f +₀ g ] (right b)
            [f+₀g]la≡[f+₀g]rb = fa≡gb
            ((s , S) , _) = f+g-emb (left a) (right b)
          in
            Eq-Copr.left-neq-right (s [f+₀g]la≡[f+₀g]rb)
        )
      )

    both-are-emb-and-neq-then-+₀-univ-map-is-emb : {A B C : Set} → {f : A → C} → {g : B → C} →
                                                   Is-emb f → Is-emb g → ((a : A) → (b : B) → ¬ (f a ≡ g b)) →
                                                   Is-emb [ f +₀ g ]
    both-are-emb-and-neq-then-+₀-univ-map-is-emb {A} {B} {C} {f} {g} f-emb g-emb neq =
      λ {
        (left a) (left a') →
          former-and-comp-are-equivs-then-latter-is-equiv
            (λ { refl → refl })
            (left-is-emb A B a a')
            (f-emb a a')
      ; (left a) (right b) →
          any-map-into-empty-type-is-equiv (λ eqn → neq a b eqn) (ap [ f +₀ g ] {left a} {right b})
      ; (right b) (left a) →
          any-map-into-empty-type-is-equiv (λ eqn → neq a b (inverse eqn)) (ap [ f +₀ g ] {right b} {left a})
      ; (right b) (right b') →
          former-and-comp-are-equivs-then-latter-is-equiv
            (λ { refl → refl })
            (right-is-emb A B b b')
            (g-emb b b')
      }

  --              top
  --         A ─────────> B
  --         │            │
  --  left  ≃│   square  ≃│  right
  --         v            v
  --         C ─────────> D
  --             bottom
  --
  -- then Is-equiv top ↔ Is-equiv bottom.
  maps-joined-with-equivs-are-equivs-iff : {A B C D : Set} →
                                          (top : A → B) → (bottom : C → D) →
                                          {left : A → C} → {right : B → D} → Is-equiv left → Is-equiv right →
                                          (square : right ∘ top ~ bottom ∘ left) →
                                          Is-equiv top ↔ Is-equiv bottom
  maps-joined-with-equivs-are-equivs-iff {A} {B} {C} {D} t b {l} {r} leqv reqv square =
    (
      --              top
      --         A ─── ≃ ───> B
      --         ∧            │
      --  left⁻¹ │≃          ≃│  right
      --         │            v
      --         C ─────────> D
      --             bottom
      (λ t-eqv →
        is-equiv-preserved-by-homotopy
          (λ c → let l⁻¹ = ≃-inverse-map-for leqv in begin
            (r ∘ t ∘ l⁻¹) c      ≡⟨ square (l⁻¹ c) ⟩
            (b ∘ l ∘ l⁻¹) c      ≡⟨ ap b (≃-inverse-map-is-sect-of-original leqv c) ⟩
            b c                  ∎
          )
          (comp-equivs-is-equiv (comp-equivs-is-equiv reqv t-eqv) (≃-inverse-map-is-equiv leqv))
      ),
      --              top
      --         A ─────────> B
      --         │            ∧
      --  left   │≃          ≃│  right⁻¹
      --         v            │
      --         C ─── ≃ ───> D
      --             bottom
      --
      (λ b-eqv →
        is-equiv-preserved-by-homotopy
          (λ c → let r⁻¹ = ≃-inverse-map-for reqv in begin
            (r⁻¹ ∘ b ∘ l) c      ≡⟨← ap r⁻¹ (square c) ⟩
            (r⁻¹ ∘ r ∘ t) c      ≡⟨ ≃-inverse-map-is-retr-of-original reqv (t c) ⟩
            t c                  ∎
          )
          (comp-equivs-is-equiv (≃-inverse-map-is-equiv reqv) (comp-equivs-is-equiv b-eqv leqv))
      )
    )

  -- exercise 11.7
  module _ where
    open +₀-Basic
    open EmptyBasic
    open Eq-Copr

    -- exercise 11.7.a
    <+₀>-is-equiv-then-both-are-equivs : {A A' B B' : Set} → (f : A → A') → (g : B → B') →
                                         Is-equiv (< f +₀ g >) → Is-equiv f × Is-equiv g
    <+₀>-is-equiv-then-both-are-equivs {A} {A'} {B} {B'} f g f+g-eqv =
      (
        has-inverse-equiv (
          f⁻¹ ,
          (λ a' → ≃-inverse-map-for (left-is-emb A' B' (f (f⁻¹ a')) a') (begin
            left (f (f⁻¹ a'))               ≡⟨⟩
            < f +₀ g > (left (f⁻¹ a'))      ≡⟨ ap < f +₀ g > (left∘f⁻¹ a') ⟩
            < f +₀ g > (<f+g>⁻¹ (left a'))  ≡⟨ ≃-inverse-map-is-sect-of-original f+g-eqv (left a') ⟩
            left a'                         ∎
          )) ,
          (λ a → ≃-inverse-map-for (left-is-emb A B (f⁻¹ (f a)) a) (begin
            left (f⁻¹ (f a))                ≡⟨ left∘f⁻¹ (f a) ⟩
            <f+g>⁻¹ (left (f a))            ≡⟨⟩
            <f+g>⁻¹ (< f +₀ g > (left a))   ≡⟨ ≃-inverse-map-is-retr-of-original f+g-eqv (left a) ⟩
            left a                          ∎
          ))
        ) ,
        has-inverse-equiv (
          g⁻¹ ,
          (λ b' → ≃-inverse-map-for (right-is-emb A' B' (g (g⁻¹ b')) b') (begin
            right (g (g⁻¹ b'))              ≡⟨⟩
            < f +₀ g > (right (g⁻¹ b'))     ≡⟨ ap < f +₀ g > (right∘g⁻¹ b') ⟩
            < f +₀ g > (<f+g>⁻¹ (right b')) ≡⟨ ≃-inverse-map-is-sect-of-original f+g-eqv (right b') ⟩
            right b'                        ∎
          )) ,
          (λ b → ≃-inverse-map-for (right-is-emb A B (g⁻¹ (g b)) b) (begin
            right (g⁻¹ (g b))               ≡⟨ right∘g⁻¹ (g b) ⟩
            <f+g>⁻¹ (right (g b))           ≡⟨⟩
            <f+g>⁻¹ (< f +₀ g > (right b))  ≡⟨ ≃-inverse-map-is-retr-of-original f+g-eqv (right b) ⟩
            right b                         ∎
          ))
        )
      )
      where
        <f+g>⁻¹ = ≃-inverse-map-for f+g-eqv
        <f+g>⁻¹-Sect = ≃-inverse-map-is-sect-of-original f+g-eqv

        f⁻¹ : A' → A
        f⁻¹ a' with <f+g>⁻¹ (left a') | <f+g>⁻¹-Sect (left a')
        ...       | left a            | _                      = a
        ...       | right b           | w                      = absurd (right-neq-left w)

        left∘f⁻¹ : (a' : A') → left (f⁻¹ a') ≡ <f+g>⁻¹ (left a')
        left∘f⁻¹ a' with <f+g>⁻¹ (left a') | <f+g>⁻¹-Sect (left a')
        ...            | left a            | _                      = refl
        ...            | right b           | w                      = absurd (right-neq-left w)

        g⁻¹ : B' → B
        g⁻¹ b' with <f+g>⁻¹ (right b') | <f+g>⁻¹-Sect (right b')
        ...       | left a             | w                       = absurd (left-neq-right w)
        ...       | right b            | _                       = b

        right∘g⁻¹ : (b' : B') → right (g⁻¹ b') ≡ <f+g>⁻¹ (right b')
        right∘g⁻¹ b' with <f+g>⁻¹ (right b') | <f+g>⁻¹-Sect (right b')
        ...             | left a             | w                       = absurd (left-neq-right w)
        ...             | right b'           | _                       = refl

    -- exercise 11.7.b
    <+₀>-is-emb-iff-both-are-embs : {A A' B B' : Set} → (f : A → A') → (g : B → B') →
                                    Is-emb (< f +₀ g >) ↔ (Is-emb f × Is-emb g)
    <+₀>-is-emb-iff-both-are-embs {A} {A'} {B} {B'} f g =
      (
        (λ f+g-emb → (
          -- left ∘ f = <f+₀g> ∘ left definitionally
          latter-and-comp-are-embs-then-comp-is-emb-iff-former-is-emb f (htpy-refl (left ∘ f))
            (left-is-emb A' B')
            (comp-embs-is-emb f+g-emb (left-is-emb A B)),
          -- right ∘ g = <f+₀g> ∘ right definitionally
          latter-and-comp-are-embs-then-comp-is-emb-iff-former-is-emb g (htpy-refl (right ∘ g))
            (right-is-emb A' B')
            (comp-embs-is-emb f+g-emb (right-is-emb A B))
        )) ,
        (λ { (f-emb , g-emb) →
          (λ {
            -- ap <f+₀g> ∘ ap left ~ ap left ∘ ap f by path induction,
            -- and since we have Is-equiv (ap left) and Is-equiv (ap f) (from f-emb)...
            (left a) (left a') →
              Σ.fst (
                maps-joined-with-equivs-are-equivs-iff
                  (ap f {a} {a'}) (ap < f +₀ g > {left a} {left a'})
                  (left-is-emb A B a a') (left-is-emb A' B' (f a) (f a'))
                  (λ { refl → refl })
              ) (f-emb a a')
          ; (left a) (right b) →
              any-map-into-empty-type-is-equiv (λ eqn → absurd (left-neq-right eqn)) _
          ; (right b) (left a) →
              any-map-into-empty-type-is-equiv (λ eqn → absurd (right-neq-left eqn)) _
          ; (right b) (right b') →
              Σ.fst (
                maps-joined-with-equivs-are-equivs-iff
                  (ap g {b} {b'}) (ap < f +₀ g > {right b} {right b'})
                  (right-is-emb A B b b') (right-is-emb A' B' (g b) (g b'))
                  (λ { refl → refl })
              ) (g-emb b b')
          })
        })
      )

  -- exercise 11.8
  module _ where
    -- exercise 11.8.a
    pointwise-homotopic-then-tot-homotopic : {A : Set} → {B C : A → Set} →
                                             (f g : (x : A) → B x → C x) →
                                             (H : (x : A) → f x ~ g x) →
                                             (totalization f ~ totalization g)
    pointwise-homotopic-then-tot-homotopic {A} {B} {C} f g H =
      λ { (x , b) → begin
        totalization f (x , b)  ≡⟨⟩
        (x , f x b)             ≡⟨ ap (λ c → (x , c)) (H x b) ⟩
        (x , g x b)             ≡⟨⟩
        totalization g (x , b)  ∎
      }

    -- exercise 11.8.b
    tot-comp : {A : Set} → {B C D : A → Set} →
               (f : (x : A) → B x → C x) → (g : (x : A) → C x → D x) →
               (totalization (λ x → g x ∘ f x) ~ totalization g ∘ totalization f)
    tot-comp {A} {B} {C} {D} f g =
      λ { (x , b) → begin
        totalization (λ x → g x ∘ f x) (x , b)     ≡⟨⟩
        (x , g x (f x b))                          ≡⟨⟩
        (totalization g ∘ totalization f) (x , b)  ∎
      }

    -- exercise 11.8.c
    tot-id : {A : Set} → {B : A → Set} → (totalization (λ x → id {B x}) ~ id)
    tot-id = λ { (x , b) → refl }

    open Equivalence.Symbolic

    fibers-retract-then-total-space-retracts : {A : Set} → {B C : A → Set} →
                                               (retrs : (x : A) → Is-retract-of (B x) (C x)) →
                                               Is-retract-of (Σ A B) (Σ A C)
    fibers-retract-then-total-space-retracts {A} {B} {C} retrs =
      let
        fns : (x : A) → B x → C x
        fns x = let (f , _) = retrs x in f

        retr-fns : (x : A) → C x → B x
        retr-fns x = let (_ , (r , _)) = retrs x in r
      in
        (
          totalization fns ,
          totalization retr-fns ,
          λ { (x , b) →
            let (_ , (_ , R)) = retrs x
            in begin
              (totalization retr-fns ∘ totalization fns) (x , b)   ≡⟨⟩
              (x , retr-fns x (fns x b))                           ≡⟨ ap (λ c → (x , c)) (R b) ⟩
              (x , b)                                              ∎
          }
        )

    -- exercise 11.8.d
    retracts-of-identities-is-equiv-to-identities : {A : Set} → (a : A) → {B : A → Set} →
                                                    (retrs : (x : A) → Is-retract-of (B x) (a ≡ x)) →
                                                    (x : A) → (let (_ , r , _) = retrs x in Is-equiv r)
    retracts-of-identities-is-equiv-to-identities {A} a {B} retrs x =
      fundamental-thm-of-identity-types.ii→i-at-fn
        (retract-of-contr-is-contr
          (fibers-retract-then-total-space-retracts retrs)
          (identity-with-an-endpoint-fixed-Is-contr a))
        (λ x → let (_ , (r , _)) = retrs x in r)
        x

    -- exercise 11.8.e
    identity-to-fiber-has-section-then-is-family-of-equivs : {A : Set} → (a : A) → {B : A → Set} →
                                                             (f : (x : A) → a ≡ x → B x) →
                                                             (sects : (x : A) → Sect (f x)) →
                                                             Is-family-of-equivs f
    identity-to-fiber-has-section-then-is-family-of-equivs {A} a {B} f sects =
      retracts-of-identities-is-equiv-to-identities
        a
        (λ x → let (s , S) = sects x in (s , f x , S))

  -- exercise 11.9
  ap-f-has-section-then-f-is-emb : {A B : Set} → (f : A → B) → ((x y : A) → Sect (ap f {x} {y})) → Is-emb f
  ap-f-has-section-then-f-is-emb {A} {B} f sects x =
    identity-to-fiber-has-section-then-is-family-of-equivs x (λ y → ap f {x} {y}) (sects x)

  -- exercise 11.10
  module _ where
    open ≡-Reasoning

    Is-path-split : {A B : Set} → (f : A → B) → Set
    Is-path-split {A} {B} f = (Sect f) × ((x y : A) → Sect (ap f {x} {y}))

    equivalence-is-path-split : {A B : Set} → {f : A → B} → Is-equiv f → Is-path-split f
    equivalence-is-path-split {A} {B} {f} f-eqv@(S , _) =
      (S , λ x y → let (S-ap , _) = is-equiv-then-is-emb f-eqv x y in S-ap)

    is-path-split-then-is-equiv : {A B : Set} → {f : A → B} → Is-path-split f → Is-equiv f
    is-path-split-then-is-equiv {A} {B} {f} ((s , S) , sects) =
      (
        (s , S) ,
        (s , (λ x →
          let fsfx≡fx       = S (f x)
              (ap-sect , _) = sects (s (f x)) x
          in ap-sect fsfx≡fx
        ))
      )

  -- exercise 11.11
  module _ where
    open Homotopy.HomotopyGroupoidSymbolic

    fib-triangle : {A B X : Set} → (h : A → B) → {f : A → X} → {g : B → X} → (H : f ~ g ∘ h) →
                   ((x : X) → fib f x → fib g x)
    fib-triangle {A} {B} {X} h {f} {g} H x (a , p) =
      (h a , ((H ⁻¹ₕₜₚ) a) · p)

    -- exercise 11.11.a
    tot-fib-triangle-fiber-gluing : {A B X : Set} → (h : A → B) → {f : A → X} → (g : B → X) → (H : f ~ g ∘ h) →
                                     glueFibers g ∘ (totalization (fib-triangle h H)) ~ h ∘ glueFibers f
    tot-fib-triangle-fiber-gluing {A} {B} {X} h {f} g H (x , (a , p)) =
      -- a `refl` works as well
      begin
        (glueFibers g ∘ (totalization (fib-triangle h H))) (x , (a , p))   ≡⟨⟩
        glueFibers g (totalization (fib-triangle h H) (x , (a , p)))       ≡⟨⟩
        glueFibers g (x , fib-triangle h H x (a , p))                      ≡⟨⟩
        glueFibers g (x , (h a , ((H ⁻¹ₕₜₚ) a) · p))                       ≡⟨⟩
        h a                                                                       ≡⟨⟩
        h (glueFibers f (x , (a , p)))                                     ≡⟨⟩
        (h ∘ glueFibers f) (x , (a , p))                                   ∎

    open ↔-Reasoning

    -- exercise 11.11.b
    equiv-iff-fib-triangle-is-equiv : {A B X : Set} → (h : A → B) → {f : A → X} → {g : B → X} → (H : f ~ g ∘ h) →
                                      Is-equiv h ↔ Is-family-of-equivs (fib-triangle h {f} {g} H)
    equiv-iff-fib-triangle-is-equiv {A} {B} {X} h {f} {g} H =
      begin-↔
        Is-equiv h                                            ↔⟨← maps-joined-with-equivs-are-equivs-iff
                                                                    (totalization (fib-triangle h {f} {g} H)) h
                                                                    (glueFibers-is-equiv f) (glueFibers-is-equiv g)
                                                                    (tot-fib-triangle-fiber-gluing h g H)
                                                              ⟩
        Is-equiv (totalization (fib-triangle h {f} {g} H))    ↔⟨← is-family-of-equivs-iff-tot-is-equiv _ ⟩
        Is-family-of-equivs (fib-triangle h {f} {g} H)        ∎-↔
