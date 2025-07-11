module _ where
  open import section-09 public

  open Homotopy
  open Homotopy.Symbolic
  open ≡-Basic
  open ≡-Reasoning

  -- 10.1.1
  Is-contr : Set → Set
  Is-contr A = Σ A (λ c → (x : A) → c ≡ x)

  two-points-eq-in-contr-type : {A : Set} → Is-contr A → (x y : A) → x ≡ y
  two-points-eq-in-contr-type (a , C) x y = (C x)⁻¹ · (C y)

  -- 10.1.2
  contraction-to : {A : Set} → (c : A) → Set
  contraction-to c = const c ~ id

  -- 10.1.3
  Unit-Is-contr : Is-contr Unit
  Unit-Is-contr = (unit , Unit-ind { λ (u : Unit) → unit ≡ u } refl)

  -- 10.1.4
  identity-with-an-endpoint-fixed-Is-contr : {A : Set} → (a : A) → Is-contr (Σ A (λ x → a ≡ x))
  identity-with-an-endpoint-fixed-Is-contr a =
    ((a , refl) , λ pt → ≡-Basic1.refl-uniq a pt)

  -- 10.2.1
  ev-pt : {A : Set} → {B : (x : A) → Set} → (a : A) → (f : (x : A) → B x) → B a
  ev-pt a f = f a

  -- 10.2.3
  contr-then-sing-ind : {A : Set} → Is-contr A → {B : A → Set} →
    Σ A (λ a → Σ (B a → (x : A) → B x) (λ ind-sing-a → ev-pt a ∘ ind-sing-a ~ id))
  contr-then-sing-ind {A} (a , C) {B} =
    let
      C' : (x : A) → a ≡ x
      C' x = (C a)⁻¹ · (C x)
      p : C' a ≡ refl
      p = ·-linv (C a)

      ind-sing-a : B a → (x : A) → B x
      ind-sing-a b x = tr B (C' x) b
      comp-sing-a : ev-pt a ∘ ind-sing-a ~ id
      comp-sing-a = λ b → begin
        (ev-pt a ∘ ind-sing-a) b ≡⟨⟩
        tr B (C' a) b            ≡⟨ ap (λ t → tr B t b) p ⟩
        tr B refl b              ≡⟨⟩
        b                        ≡⟨⟩
        id b                     ∎
    in
      (a , ind-sing-a , comp-sing-a)

  -- 10.2.3
  -- To properly phrase "singleton induction" we need to use Set₁ and the corresponding
  -- (or universe-polymorphic) Σ types, but for our purposes it suffices to consider
  -- just one type family B(x) := a ≡ x, since that is the only induction we will use.
  sing-ind-on-identity-then-contr : {A : Set} →
    Σ A (λ a → Σ (a ≡ a → (x : A) → a ≡ x) (λ ind-sing-a → ev-pt a ∘ ind-sing-a ~ id)) →
    Is-contr A
  sing-ind-on-identity-then-contr (a , ind-sing-a , _) =
    (a , λ x → ind-sing-a refl x)

  -- 10.3.1
  fib : {A B : Set} → (f : A → B) → (b : B) → Set
  fib {A} {B} f b = Σ A (λ a → f a ≡ b)

  -- 10.3.2
  Eq-fib : {A B : Set} → (f : A → B) → {y : B} → fib f y → fib f y → Set
  Eq-fib f (x , p) (x' , p') = Σ (x ≡ x') (λ α → p ≡ (ap f α) · p')

  Eq-fib-refl : {A B : Set} → (f : A → B) → {y : B} → (x : fib f y) → Eq-fib f x x
  Eq-fib-refl f (x , p) = (refl , refl)

  Eq-fib-from-identity : {A B : Set} → (f : A → B) → {y : B} →
                         {x x' : fib f y} → (p : x ≡ x') → Eq-fib f x x'
  Eq-fib-from-identity f refl = Eq-fib-refl f _

  open Equivalence

  identity-from-Eq-fib : {A B : Set} → (f : A → B) → {y : B} → {x x' : fib f y} →
    Eq-fib f x x' → x ≡ x'
  identity-from-Eq-fib f (refl , refl) = refl

  -- 10.3.3
  Eq-fib-from-identity-is-equiv : {A B : Set} → (f : A → B) → {y : B} → {x x' : fib f y} →
                                  Is-equiv (Eq-fib-from-identity f {y} {x} {x'})
  Eq-fib-from-identity-is-equiv f {y} {x} {x'} =
    has-inverse-equiv (identity-from-Eq-fib f , rinverse , linverse)
    where
      rinverse : (Eq-fib-from-identity f) ∘ (identity-from-Eq-fib f) ~ id
      rinverse (refl , refl) = refl
      linverse : (identity-from-Eq-fib f) ∘ (Eq-fib-from-identity f) ~ id
      linverse refl = refl

  -- 10.3.4
  Is-contr-fn : {A B : Set} → (f : A → B) → Set
  Is-contr-fn {A} {B} f = (b : B) → Is-contr (fib f b)

  open Σ

  -- 10.3.5
  contr-fn-then-equiv : {A B : Set} → (f : A → B) → Is-contr-fn f → Is-equiv f
  contr-fn-then-equiv {A} {B} f contr =
    let
      gG : (y : B) → fib f y
      gG y = contr y .fst
      g : B → A
      g y = gG y .fst
      G : (y : B) → f (g y) ≡ y
      G y = gG y .snd

      linverse : g ∘ f ~ id
      linverse x =
        let
          (_ , C) = contr (f x)
          q = begin
            -- the LHS is THE center of contraction of fib f (f x)
            (g (f x) , G (f x))   ≡⟨ C (x , refl) ⟩
            (x , refl)            ∎
        in ap fst q
    in has-inverse-equiv (g , G , linverse)

  -- 10.4.1
  Is-coh-invertible : {A B : Set} → (f : A → B) → Set
  Is-coh-invertible {A} {B} f =
    Σ (Has-inverse f) (λ { (g , G , H) → lwhisker G f ~ rwhisker f H })

  -- 10.4.2
  coh-invertible-then-contr-fn : {A B : Set} → (f : A → B) → Is-coh-invertible f → Is-contr-fn f
  coh-invertible-then-contr-fn {A} {B} f ((g , G , H) , K) y =
    (center , C)
    where
      center : fib f y
      center = (g y , G y)
      C' : (x : fib f y) → Eq-fib f center x
      C' (x , refl) = (H x , K')
        where
          K' : G (f x) ≡ ap f (H x) · refl
          K' = begin
            G (f x)             ≡⟨ K x ⟩
            ap f (H x)          ≡⟨← (·-runit _) ⟩
            ap f (H x) · refl   ∎
      C : (x : fib f y) → center ≡ x
      C x = identity-from-Eq-fib f (C' x)

  -- 10.4.4
  comm-htpy : {A : Set} → (f : A → A) → (H : f ~ id) → (x : A) → (H (f x) ≡ ap f (H x))
  comm-htpy f H x = begin
    H (f x)                           ≡⟨← (·-runit (H (f x))) ⟩
    H (f x) · refl                    ≡⟨← ap (λ p → H (f x) · p) (·-rinv (H x)) ⟩
    H (f x) · (H x · (H x)⁻¹)         ≡⟨ unassoc (H (f x)) (H x) ((H x)⁻¹) ⟩
    H (f x) · H x · (H x)⁻¹           ≡⟨← ap (λ p → H (f x) · p · (H x)⁻¹) (ap-id (H x)) ⟩
    H (f x) · ap id (H x) · (H x)⁻¹   ≡⟨← ap (λ p → p · (H x)⁻¹) (nat-htpy H (H x)) ⟩
    ap f (H x) · H x · (H x)⁻¹        ≡⟨ assoc (ap f (H x)) (H x) ((H x)⁻¹) ⟩
    ap f (H x) · (H x · (H x)⁻¹)      ≡⟨ ap (λ p → ap f (H x) · p) (·-rinv (H x)) ⟩
    ap f (H x) · refl                 ≡⟨ ·-runit _ ⟩
    ap f (H x)                        ∎

  --   ┊   │     │   ┊  
  --  [H]  │  =  │  [H] 
  --   │   │     │   │  
  --   f   f     f   f  
  comm-htpy-whisk : {A : Set} → (f : A → A) → (H : f ~ id) → (lwhisker H f ~ rwhisker f H)
  comm-htpy-whisk = comm-htpy

  open Homotopy.Reasoning

  Is-coh-invertible-then-inverse-is-coh-invertible : {A B : Set} →
        (f : A → B) → (g : B → A) → (G : f ∘ g ~ id) → (H : g ∘ f ~ id) → 
        (lwhisker G f ~ rwhisker f H) →
        (lwhisker H g ~ rwhisker g G) -- this makes ((f , H , G) , ∙) : Is-coh-invertible g
  Is-coh-invertible-then-inverse-is-coh-invertible {A} {B} f g G H K =
    begin-htpy
      --   ┊    │
      -- ╭[H]╮  │
      -- │   │  │
      -- g   f  g
      lwhisker H g

              ~⟨← hcomp-lunit (lwhisker H g) ⟩
      --  ┊    ┊    │
      --  ┊  ╭[H]╮  │
      --  ┊  │   │  │
      --     g   f  g
      hcomp (htpy-refl id) (lwhisker H g)

                ~⟨← hcomp-lhtpe (·ₕₜₚ-linv H) _ ⟩
      --    ┊       ┊    │
      --    ┊     ╭[H]╮  │
      -- ╭─[H]─╮  │   │  │
      -- g     f  │   │  │
      -- ╰[H⁻¹]╯  │   │  │
      --    ┊     │   │  │
      --          g   f  g
      (            hcomp (H ⁻¹ₕₜₚ ·ₕₜₚ H) (lwhisker H g)              )  ~⟨ hcomp-lconcat (H ⁻¹ₕₜₚ) H (lwhisker H g) ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (hcomp    H (lwhisker H g))  ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (hcomp-lr H (lwhisker H g))

                    ~⟨ ·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (hcomp-lr-rl H (lwhisker H g)) ⟩
      --    ┊       ┊    │
      -- ╭─[H]─╮    ┊    │
      -- │     │    ┊    │
      -- g     f  ╭[H]╮  │
      -- ╰[H⁻¹]╯  │   │  │
      --    ┊     │   │  │
      --          g   f  g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (              hcomp-rl H (lwhisker H g)              )     ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ ((rwhisker (g ∘ f) (lwhisker H g)) ·ₕₜₚ (lwhisker H g))     ~⟨ ·ₕₜₚ-unassoc (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) _ _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (rwhisker (g ∘ f) (lwhisker H g)) ·ₕₜₚ (lwhisker H g)      ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (
                                                                                                            begin-htpy
                                                                                                              rwhisker (g ∘ f) (lwhisker H g)          ~⟨ rwhisker-comp g f _ ⟩
                                                                                                              rwhisker g (rwhisker f (lwhisker H g))   ~⟨⟩
                                                                                                              rwhisker g (lwhisker (rwhisker f H) g)   ∎-htpy
                                                                                                            )) _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker (rwhisker f H) g)) ·ₕₜₚ (lwhisker H g)

                    ~⟨← ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (rwhisker-rhtpe _ (lwhisker-lhtpe K _))) _ ⟩
      --    ┊             │
      -- ╭─[H]─────────╮  │
      -- g     ╭[G]╮   │  │
      -- ╰[H⁻¹]╯   │   │  │
      --    ┊      │   │  │
      --           g   f  g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker (lwhisker G f) g)) ·ₕₜₚ (lwhisker H g) ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker g (lwhisker G (f ∘ g)))        ·ₕₜₚ (lwhisker H g)

                    ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (rwhisker-rhtpe _ (comm-htpy-whisk (f ∘ g) G))) _ ⟩
      --    ┊     │     ┊  
      -- ╭─[H]─╮  │     ┊  
      -- g     │  │   ╭[G]╮
      -- ╰[H⁻¹]╯  │   │   │
      --    ┊     │   │   │
      --          g   f   g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (rwhisker g (rwhisker (f ∘ g) G)) ·ₕₜₚ (lwhisker H g)    ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (
                                                                                                          begin-htpy
                                                                                                            rwhisker g (rwhisker (f ∘ g) G)          ~⟨ rwhisker-rhtpe g (rwhisker-comp f g G) ⟩
                                                                                                            rwhisker g (rwhisker f (rwhisker g G))   ~⟨← rwhisker-comp g f _ ⟩
                                                                                                            rwhisker (g ∘ f) (rwhisker g G)          ∎-htpy
                                                                                                         )) _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (rwhisker (g ∘ f) (rwhisker g G)) ·ₕₜₚ (lwhisker H g)    ~⟨ ·ₕₜₚ-assoc (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) _ _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ ((rwhisker (g ∘ f) (rwhisker g G)) ·ₕₜₚ (lwhisker H g))   ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (              hcomp-rl H (rwhisker g G)              )

                    ~⟨← ·ₕₜₚ-rhtpe (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) (hcomp-lr-rl H (rwhisker g G)) ⟩
      --    ┊     │     ┊  
      --    ┊     │   ╭[G]╮
      -- ╭─[H]─╮  │   │   │
      -- ╰[H⁻¹]╯  │   │   │
      --    ┊     │   │   │
      --          g   f   g
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ (                hcomp-lr H (rwhisker g G)                 )   ~⟨⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ ((lwhisker H (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker id (rwhisker g G)))   ~⟨ ·ₕₜₚ-unassoc (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) _ _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ) (g ∘ f ∘ g)) ·ₕₜₚ  (lwhisker H (g ∘ f ∘ g)) ·ₕₜₚ (rwhisker id (rwhisker g G))    ~⟨← ·ₕₜₚ-lhtpe (lwhisker-concat (H ⁻¹ₕₜₚ) H (g ∘ f ∘ g)) _ ⟩
      (lwhisker (H ⁻¹ₕₜₚ ·ₕₜₚ H) (g ∘ f ∘ g))                         ·ₕₜₚ (rwhisker id (rwhisker g G))    ~⟨⟩
      hcomp (H ⁻¹ₕₜₚ ·ₕₜₚ H) (rwhisker g G)

              ~⟨ hcomp-lhtpe (·ₕₜₚ-linv H) _ ⟩
      -- ┊  │     ┊  
      -- ┊  │   ╭[G]╮
      -- ┊  │   │   │
      --    g   f   g
      hcomp (htpy-refl id) (rwhisker g G)

              ~⟨ hcomp-lunit (rwhisker g G) ⟩
      -- │     ┊  
      -- │   ╭[G]╮
      -- │   │   │
      -- g   f   g
      rwhisker g G   ∎-htpy

  -- 10.4.5
  Has-inverse-then-Is-coh-invertible : {A B : Set} → (f : A → B) → Has-inverse f → Is-coh-invertible f
  Has-inverse-then-Is-coh-invertible {A} {B} f (g , G , H) =
    let
      -- ╭───────────[G]╮ 
      -- │              │ 
      -- │      ╭─[H]╮  │ 
      -- ╰[G⁻¹]─╯    │  │ 
      --             │  │ 
      --             f  g 
      G' : f ∘ g ~ id
      G' = lwhisker (G ⁻¹ₕₜₚ) (f ∘ g) ·ₕₜₚ (rwhisker f (lwhisker H g)) ·ₕₜₚ G

      K : lwhisker G' f ~ rwhisker f H
      K =
        begin-htpy
          --              ┊    │
          -- ╭───────────[G]╮  │
          -- │              │  │
          -- │      ╭─[H]╮  │  │
          -- ╰[G⁻¹]─╯    │  │  │
          --             │  │  │
          --             f  g  f
          lwhisker G' f                                                                                        ~⟨⟩
          lwhisker ((lwhisker (G ⁻¹ₕₜₚ) (f ∘ g)) ·ₕₜₚ (rwhisker f (lwhisker H g)) ·ₕₜₚ G) f                    ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (lwhisker (rwhisker f (lwhisker H g)) f) ·ₕₜₚ (lwhisker G f)   ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f (lwhisker H (g ∘ f))) ·ₕₜₚ (lwhisker G f)          

                  ~⟨ ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) (rwhisker-rhtpe f
                      (comm-htpy-whisk (g ∘ f) H)
                    )) _ ⟩
          --     ┊     │     ┊   
          --  ╭─[G]─╮  │     ┊   
          --  │     │  │   ╭[H]╮ 
          --  ╰[G⁻¹]╯  │   │   │ 
          --     ┊     │   │   │ 
          --           f   g   f 
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f (rwhisker (g ∘ f) H)) ·ₕₜₚ (lwhisker G f)           ~⟨← ·ₕₜₚ-lhtpe (·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) (rwhisker-comp f (g ∘ f) H)) _ ⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ  (rwhisker (f ∘ g ∘ f) H) ·ₕₜₚ (lwhisker G f)                   ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ  (rwhisker (f ∘ g ∘ f) H) ·ₕₜₚ (lwhisker (lwhisker G f) id)     ~⟨ ·ₕₜₚ-assoc (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) _ _ ⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ ((rwhisker (f ∘ g ∘ f) H) ·ₕₜₚ (lwhisker (lwhisker G f) id))    ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (                hcomp-rl (lwhisker G f) H                 )    

                  ~⟨← ·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) (hcomp-lr-rl (lwhisker G f) H) ⟩
          --     ┊     │     ┊  
          --     ┊     │   ╭[H]╮
          --  ╭─[G]─╮  │   │   │
          --  ╰[G⁻¹]╯  │   │   │
          --     ┊     │   │   │
          --           f   g   f
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ (hcomp-lr (lwhisker G f) H)                              ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ ((lwhisker (lwhisker G f) (g ∘ f)) ·ₕₜₚ (rwhisker f H))  ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ ((lwhisker G (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f H))           ~⟨ ·ₕₜₚ-unassoc (lwhisker (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g)) f) _ _ ⟩
          (lwhisker (G ⁻¹ₕₜₚ) (f ∘ g ∘ f)) ·ₕₜₚ  (lwhisker G (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f H)            ~⟨⟩
          (lwhisker (G ⁻¹ₕₜₚ  ·ₕₜₚ G) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker f H)                                   ~⟨← ·ₕₜₚ-rhtpe (lwhisker (G ⁻¹ₕₜₚ  ·ₕₜₚ G) (f ∘ g ∘ f)) (rwhisker-id (rwhisker f H)) ⟩
          (lwhisker (G ⁻¹ₕₜₚ  ·ₕₜₚ G) (f ∘ g ∘ f)) ·ₕₜₚ (rwhisker id (rwhisker f H))                     ~⟨⟩
          hcomp (G ⁻¹ₕₜₚ ·ₕₜₚ G) (rwhisker f H)

                  ~⟨ hcomp-lhtpe (·ₕₜₚ-linv G) _ ⟩
          --  ┊  │     ┊  
          --  ┊  │   ╭[H]╮
          --  ┊  │   │   │
          --     f   g   f
          hcomp (htpy-refl id) (rwhisker f H)

                  ~⟨ hcomp-lunit _ ⟩
          -- │     ┊  
          -- │   ╭[H]╮
          -- │   │   │
          -- f   g   f
          rwhisker f H ∎-htpy
    in ((g , G' , H) , K)

  -- 10.4.6
  Is-equiv-then-is-contr : {A B : Set} → (f : A → B) → Is-equiv f → Is-contr-fn f
  Is-equiv-then-is-contr {A} {B} f is-eqv =
    let
      has-inv     = equiv-has-inverse is-eqv
      is-coh-inv  = Has-inverse-then-Is-coh-invertible f has-inv
      is-contr-fn = coh-invertible-then-contr-fn f is-coh-inv
    in is-contr-fn

  -- 10.4.7
  inverse-paths-type-is-contr : {A : Set} → (a : A) → Is-contr (Σ A (λ x → x ≡ a))
  inverse-paths-type-is-contr {A} a =
    let
      id-is-contr-fn : Is-contr-fn id
      id-is-contr-fn = Is-equiv-then-is-contr id (Equivalence.id-is-equiv)
    in id-is-contr-fn a -- `Σ A (λ x → x ≡ a)` is judgementally equal to `fib id a`

  -- exercise 10.1
  module _ where
    ap-const-refl : {A : Set} → (c : A) → {x y : A} → (p : x ≡ y) → ap (const c) p ≡ refl
    ap-const-refl c {x} {_} refl = refl

    Is-contr-then-based-loop-space-is-contr : {A : Set} → Is-contr A → (x : A) → Is-contr (x ≡ x)
    Is-contr-then-based-loop-space-is-contr {A} (a , C) x =
      let
        H : const x ~ id
        H = λ y → (C x)⁻¹ · (C y)
        Hx-refl : H x ≡ refl
        Hx-refl = ·-linv (C x)
      in (
        refl-at x ,
        λ p →
          begin
            refl-at x                                ≡⟨⟩
            refl · refl                              ≡⟨← ap (λ q → q · refl) (ap-const-refl x p) ⟩
            ap (const x) p · refl                    ≡⟨← ap (λ q → ap (const x) p · q) (Hx-refl) ⟩
            ap (const x) p · H x                     ≡⟨ nat-htpy H p ⟩
            H x · (ap id p)                          ≡⟨ ap (λ q → q · (ap id p)) (Hx-refl) ⟩
            refl · (ap id p)                         ≡⟨ ·-lunit (ap id p) ⟩
            ap id p                                  ≡⟨ ap-id p ⟩
            p                                        ∎
      )

    Is-contr-then-identity-is-contr : {A : Set} → Is-contr A → (x y : A) → Is-contr (x ≡ y)
    Is-contr-then-identity-is-contr {A} (a , C) x y =
      let
        H : const x ~ id
        H = λ y → (C x)⁻¹ · (C y)
        Hx-refl : H x ≡ refl
        Hx-refl = ·-linv (C x)
      in (
        (two-points-eq-in-contr-type (a , C) x y),
        λ { refl →
          {!   !}
        }
      )

  -- exercise 10.2
  retraction-preserves-contr : {A B : Set} → {f : A → B} → Retr f → Is-contr B → Is-contr A
  retraction-preserves-contr {A} {B} {f} (g , G) (bc , bC) =
    (g bc , λ a → begin
      g bc       ≡⟨ ap g (bC (f a)) ⟩
      g (f a)    ≡⟨ G a ⟩
      a          ∎
    )

  -- exercise 10.3.a
  const-unit-is-equiv-then-contr : {A : Set} → Is-equiv (λ (a : A) → const unit a) → Is-contr A
  const-unit-is-equiv-then-contr {A} (_ , retr) = retraction-preserves-contr retr Unit-Is-contr

  contr-then-const-unit-is-equiv : {A : Set} → Is-contr A → Is-equiv (λ (a : A) → const unit a)
  contr-then-const-unit-is-equiv {A} (ac , C) =
    has-inverse-equiv ((λ _ → ac) , (λ { unit → refl }) , C)

  -- TODO: exercise 10.3.b

  -- exercise 10.4
  module _ where
    open EmptyBasic

    inhabited-sum-is-not-contr : {A B : Set} → A → B → ¬ Is-contr (A +₁ B)
    inhabited-sum-is-not-contr _ b (left c , C) = Eq-Copr.left-neq-right (C (right b))
    inhabited-sum-is-not-contr a _ (right c , C) = Eq-Copr.left-neq-right ((C (left a)) ⁻¹)

    fin-is-not-contr-except-fin-one : {n : Nat} → (n ≢ succ zero) → ¬ (Is-contr (Fin n))
    fin-is-not-contr-except-fin-one {zero}           _    ()
    fin-is-not-contr-except-fin-one {succ zero}     neq   _   = neq refl
    fin-is-not-contr-except-fin-one {succ (succ n)}  _  contr = inhabited-sum-is-not-contr (right unit) unit contr

  -- exercise 10.5
  both-contr-then-product-is-contr : {A B : Set} → Is-contr A → Is-contr B → Is-contr (A × B)
  both-contr-then-product-is-contr {A} {B} (ca , CA) (cb , CB) =
    ((ca , cb) , λ (x , y) → begin
      (ca , cb)           ≡⟨ ap2 (λ a b → (a , b)) (CA x) (CB y) ⟩
      (x , y)             ∎
    )
  product-is-contr-then-both-contr : {A B : Set} → Is-contr (A × B) → Is-contr A × Is-contr B
  product-is-contr-then-both-contr {A} {B} (cab , CAB) =
    let
      ca = fst cab
      cb = snd cab
    in (
      (ca , λ a → ap fst (CAB (a , cb))),
      (cb , λ b → ap snd (CAB (ca , b)))
    )

  -- exercise 10.6
  base-is-contr-then-pair-with-base-is-equiv : {A : Set} → ((a , C) : Is-contr A) →
                                               {B : A → Set} → Is-equiv {B a} {Σ A B} (λ (y : B a) → (a , y))
  base-is-contr-then-pair-with-base-is-equiv {A} (a , C) {B} =
    has-inverse-equiv ({!   !} , {!   !} , {!   !})
    where
      f : B a → Σ A B
      f y = (a , y)
      g : Σ A B → B a
      g (a' , y) with C a'
      ...           | refl = y
