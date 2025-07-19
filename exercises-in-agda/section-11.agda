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
        (Is-equiv-then-is-contr f-is-eqv (Σ.fst t))
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

