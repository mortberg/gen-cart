{-

Definition of (weak) Glue and their (unaligned) fibrancy.

-}
{-# OPTIONS --rewriting #-}
module glueing.core where

open import prelude
open import interval
open import cofprop
open import fibrations
open import equivs
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Glueing
----------------------------------------------------------------------
<_,id> : ∀{ℓ}{Γ : Set ℓ} → Γ → Int → Γ × Int
< x ,id> i = (x , i)

record Glue (Φ : CofProp)
  (T : [ Φ ] → Set)
  (A : Set)
  (f : (u : [ Φ ]) → T u → A) : Set
  where
  constructor glue
  field
    dom : (u : [ Φ ]) → T u
    cod : A
    match : (u : [ Φ ]) → f u (dom u) ≡ cod

open Glue public

Glue' :
  ∀{a}{Γ : Set a}
  (Φ : Γ → CofProp)
  (T : res Γ Φ → Set)
  (A : Γ → Set)
  (f : (xu : res Γ Φ) → T xu → A (xu .fst))
  → ---------------
  Γ → Set
Glue' Φ T A f x = Glue (Φ x) (λ u → T (x , u)) (A x) (λ u → f (x , u))

glueExt :
  {Φ : CofProp}
  {T : [ Φ ] → Set}
  {A : Set}
  (f : (u : [ Φ ]) → T u → A)
  (g g' : Glue Φ T A f)
  (p : g .dom ≡ g' .dom)
  (q : g .cod ≡ g' .cod)
  → ---------------
  g ≡ g'
glueExt _ (glue t a ft≡a) (glue _ _ ft≡a') refl refl =
  cong (glue t a) (funext λ u → uip (ft≡a u) (ft≡a' u))

FibGlueId :
  (Φ : Int → CofProp)
  {T : res Int Φ → Set}
  {A : Int → Set}
  (f : (xu : res Int Φ) → T xu → A (xu .fst))
  (e : Equiv' f)
  → ---------------
  isFib T → isFib A → isFib (Glue' Φ T A f)
FibGlueId Φ {T} {A} f e τ α r p ψ q (glue t₀ a₀ ft₀↗a₀ , ext) =
  record
  { comp = λ s →
    ( glue
      (λ us → R s us .comp O (I≡IsCofProp O) .fst .fst)
      (wA' s .comp O (I≡IsCofProp O) .fst)
      (λ us →
        trans
          (wA' s .comp O (I≡IsCofProp O) .snd ∣ inl us ∣)
          (symm (R s us .comp O (I≡IsCofProp O) .fst .snd .atO)))
    , λ v →
      glueExt (λ u → f (p s , u)) _ _
        (funext λ us →
          cong fst
            (trans
              (R s us .comp O (I≡IsCofProp O) .snd v)
              (symm (C₂ s us (RFiber s us v) .atO))))
        (wA' s .comp O (I≡IsCofProp O) .snd ∣ inr v ∣)
    )
  ; cap =
    ( path
      (λ t →
        glue
          (λ ur → R̲ t ur .fst .fst)
          (w̲A' t .fst)
          (λ ur →
            trans
              (w̲A' t .snd ∣ inl ur ∣)
              (symm (R̲ t ur .fst .snd .atO))))
      (glueExt (λ u → f (p r , u)) _ _
        (funext λ ur →
          trans
            (symm (fiberDomEqDep (wAr≡dO O ur refl) refl))
            (symm (cong fst (R̲ O ur .snd ∣ inl refl ∣))))
        (symm (w̲A' O .snd ∣ inr ∣ inl refl ∣ ∣)))
      (glueExt (λ u → f (p r , u)) _ _
        (funext λ ur →
          trans
            (cong fst (C̲₂ I ur (R̲Fiber I ur ∣ inl refl ∣) .atO))
            (symm (cong fst (R̲ I ur .snd ∣ inr ∣ inl refl ∣ ∣))))
        (trans
          (symm (d I .snd ∣ inr ∣ inl refl ∣ ∣))
          (symm (w̲A' I .snd ∣ inr ∣ inr ∣ inl refl ∣ ∣ ∣))))
    , λ t v →
      glueExt (λ u → f (p r , u)) _ _
        (funext λ ur →
          trans
            (cong fst (R̲ t ur .snd ∣ inr ∣ inr v ∣ ∣))
            (symm (cong fst (C̲₂ t ur (R̲Fiber t ur ∣ inr v ∣) .atO))))
        (trans
          (w̲A' t .snd ∣ inr ∣ inr ∣ inr v ∣ ∣ ∣)
          (trans
            (d t .snd ∣ inr ∣ inr v ∣ ∣)
            (cong cod (ext v))))
    )
  }

  where
  -- Step 4

  wATube : [ ψ ] → (i : Int) → A (p i)
  wATube v i = q v i .cod

  wABase : A (p r) [ ψ ↦ wATube ◆ r ]
  wABase = (a₀ , λ v → cong cod (ext v))

  wA = α r p ψ wATube wABase

  -- Step 5

  module _ (s : Int) where

    module _ (us : [ Φ (p s) ]) where

      C₁ = e (p s , us) (wA .comp s .fst) .fst
      C₂ = e (p s , us) (wA .comp s .fst) .snd

  -- Step 6

      σ : isFib (Fiber (f (p s , us)))
      σ =
        FibΣ {B = λ{ (a , t) → f (p s , us) t ~ a}}
          (reindex T τ (λ _ → p s , us))
          (reindex (Path A) (FibPath α) (λ{ (a , t) → (p s , f (p s , us) t , a)}))


      RFiber : [ ψ ] → Fiber (f (p s , us)) (wA .comp s .fst)
      RFiber v =
        ( q v s .dom us
        , path
          (λ _ → wA .comp s .fst)
          (trans
            (symm (q v s .match us))
            (symm (wA .comp s .snd v)))
          refl
        )

      RTube : [ ψ ] → Int → Fiber (f (p s , us)) (wA .comp s .fst)
      RTube uv k = C₂ (RFiber uv) .at k

      RBase : Fiber (f (p s , us)) (wA .comp s .fst) [ ψ ↦ RTube ◆ I ]
      RBase = ( C₁ , λ uv → C₂ (RFiber uv) .atI)

      R = strictifyFib (Fiber (f (p s , us))) σ I (λ _ → wA .comp s .fst) ψ RTube RBase

  -- Step 7

    wA'Tube : [ Φ (p s) ∨ ψ ] → Int → A (p s)
    wA'Tube =
      ∨-rec (Φ (p s)) ψ
        (λ us k → R us .comp O (I≡IsCofProp O) .fst .snd .at k)
        (λ v _ → q v s .cod)
        (λ us v → funext λ k →
          trans
            (symm (wA .comp s .snd v))
            (cong (λ fib → fib .snd .at k)
              (trans
                (C₂ us (RFiber us v) .atO)
                (symm (R us .comp O (I≡IsCofProp O) .snd v)))))

    wA'Base : A (p s) [ Φ (p s) ∨ ψ ↦ wA'Tube ◆ I ]
    wA'Base =
      ( wA .comp s .fst
      , ∨-elimEq (Φ (p s)) ψ
          (λ us → R us .comp O (I≡IsCofProp O) .fst .snd .atI)
          (λ v → wA .comp s .snd v)
      )

    wA' = strictifyFib A α I (λ _ → p s) (Φ (p s) ∨ ψ) wA'Tube wA'Base

  -- Step 4̲

  module _ (t : Int) where

    dTube : [ t ≈O ∨ t ≈I ∨ ψ ] → Int → A (p r)
    dTube =
      ∨-rec (t ≈O) (t ≈I ∨ ψ)
        (λ t≡O j → wA .cap .fst .at j)
        (λ _ _ → a₀)
        (λ {refl → ∨-elimEq (t ≈I) ψ
          (λ t≡I → O≠I t≡I)
          (λ v → funext λ j →
            trans
              (cong cod (ext v))
              (symm (wA .cap .snd j v)))})

    dBase : A (p r) [ t ≈O ∨ t ≈I ∨ ψ ↦ dTube ◆ I ]
    dBase =
      ( a₀
      , ∨-elimEq (t ≈O) (t ≈I ∨ ψ)
          (λ {refl → wA .cap .fst .atI})
          (λ _ → refl)
      )

    d = α I (λ _ → p r) (t ≈O ∨ t ≈I ∨ ψ) dTube dBase .comp O
    
  -- Step 5̲

    module _ (ur : [ Φ (p r) ]) where

      C̲₁ = e (p r , ur) (d .fst) .fst
      C̲₂ = e (p r , ur) (d .fst) .snd

  -- Step 6̲

      R̲Fiber : [ t ≈I ∨ ψ ] → Fiber (f (p r , ur)) (d .fst)
      R̲Fiber =
        ∨-rec (t ≈I) (ψ)
          (λ {refl →
            ( t₀ ur
            , path
              (λ _ → d .fst)
              (trans
                (symm (ft₀↗a₀ ur))
                (symm (d .snd ∣ inr ∣ inl refl ∣ ∣)))
              refl
            )})
          (λ v →
              ( q v r .dom ur
              , path
                (λ _ → d .fst)
                (trans
                  (trans
                    (symm (q v r .match ur))
                    (symm (cong cod (ext v))))
                  (symm (d .snd ∣ inr ∣ inr v ∣ ∣)))
                refl
              ))
          (λ {refl v →
                FiberExt
                  (symm (cong (λ g → g .dom ur) (ext v)))
                  refl})

      wAr≡dO : t ≡ O → wA .comp r .fst ≡ d .fst
      wAr≡dO t≡O = trans (d .snd ∣ inl t≡O ∣) (symm (wA .cap .fst .atO))

      dO≡wAr : t ≡ O →  d .fst ≡ wA .comp r .fst
      dO≡wAr t≡O = trans (wA .cap .fst .atO) (symm (d .snd ∣ inl t≡O ∣))

      R̲FiberAtO : (t≡O : t ≡ O) (v : [ ψ ])
        → subst (Fiber (f (p r , ur))) (wAr≡dO t≡O) (RFiber r ur v) ≡ R̲Fiber ∣ inr v ∣
      R̲FiberAtO refl v =
        FiberExtDep (wAr≡dO refl) refl (funext λ _ → wAr≡dO refl)

      R̲Tube : [ t ≈O ∨ t ≈I ∨ ψ ] → Int → Fiber (f (p r , ur)) (d .fst)
      R̲Tube =
        ∨-rec (t ≈O) (t ≈I ∨ ψ)
          (λ t≡O k →
            subst (Fiber (f (p r , ur)))
              (wAr≡dO t≡O)
              (R r ur .comp k (I≡IsCofProp k) .fst))
          (λ w k → C̲₂ (R̲Fiber w) .at k)
          (λ {refl →
            ∨-elimEq (t ≈I) ψ
              (λ t≡I → O≠I t≡I)
              (λ v → funext λ k →
                trans
                  (congdep₂
                    (λ b fib → e (p r , ur) b .snd fib .at k)
                    (wAr≡dO refl)
                    (FiberExtDep (wAr≡dO refl) refl (funext λ _ → wAr≡dO refl)))
                  (cong (subst (Fiber (f (p r , ur))) (wAr≡dO refl))
                    (symm (R r ur .comp k (I≡IsCofProp k) .snd v))))})

      R̲Base : _ [ t ≈O ∨ t ≈I ∨ ψ ↦ R̲Tube ◆ I ]
      R̲Base =
        ( C̲₁
        , ∨-elimEq (t ≈O) (t ≈I ∨ ψ)
            (λ {refl →
              trans
                (congdep (λ b → e (p r , ur) b .fst) (wAr≡dO refl))
                (cong (subst (Fiber (f (p r , ur))) (wAr≡dO refl))
                  (R r ur .cap (I≡IsCofProp I)))})
            (λ Iuv → C̲₂ (R̲Fiber Iuv) .atI)
        )

      R̲ = σ r ur I (λ _ → d .fst) (t ≈O ∨ t ≈I ∨ ψ) R̲Tube R̲Base .comp O

    w̲A'Tube : [ Φ (p r) ∨ t ≈O ∨ t ≈I ∨ ψ ] → Int → A (p r)
    w̲A'Tube =
      ∨-rec (Φ (p r)) (t ≈O ∨ t ≈I ∨ ψ)
        (λ ur k → R̲ ur .fst .snd .at k)
        (∨-rec (t ≈O) (t ≈I ∨ ψ)
          (λ {refl k → wA' r .comp k (I≡IsCofProp k) .fst})
          (λ _ _ → d .fst)
          (λ {refl →
            ∨-elimEq (t ≈I) ψ
              (λ t≡I → O≠I t≡I)
              (λ v → funext λ k →
                trans
                  (d .snd ∣ inr ∣ inr v ∣ ∣)
                  (trans
                    (cong cod (ext v))
                    (symm (wA' r .comp k (I≡IsCofProp k) .snd ∣ inr v ∣))))}))
        (λ ur → ∨-elimEq (t ≈O) (t ≈I ∨ ψ)
          (λ {refl → funext λ k →
            trans
              (wA' r .comp k (I≡IsCofProp k) .snd ∣ inl ur ∣)
              (trans
                (symm (fiberPathEqDep (wAr≡dO ur refl) refl k))
                (symm (fiberPathEq (R̲ ur .snd ∣ inl refl ∣) k)))})
          (∨-elimEq (t ≈I) ψ
            (λ {refl → funext λ k →
              fiberPathEq
                (trans
                  (C̲₂ ur (R̲Fiber ur ∣ inl refl ∣) .atO)
                  (symm (R̲ ur .snd ∣ inr ∣ inl refl ∣ ∣)))
                k})
            (λ v → funext λ k →
              fiberPathEq
                (trans
                  (C̲₂ ur (R̲Fiber ur ∣ inr v ∣) .atO)
                  (symm (R̲ ur .snd ∣ inr ∣ inr v ∣ ∣)))
                k)))

    w̲A'Base : A (p r) [ Φ (p r) ∨ t ≈O ∨ t ≈I ∨ ψ ↦ w̲A'Tube ◆ I ]
    w̲A'Base =
      ( d .fst
      , ∨-elimEq (Φ (p r)) (t ≈O ∨ t ≈I ∨ ψ)
          (λ ur → R̲ ur .fst .snd .atI)
          (∨-elimEq (t ≈O) (t ≈I ∨ ψ)
            (λ {refl →
              trans
                (d .snd ∣ inl refl ∣)
                (trans
                  (symm (wA .cap .fst .atO))
                  (wA' r .cap (I≡IsCofProp I)))})
            (λ _ → refl))
      )

    w̲A' = α I (λ _ → p r) (Φ (p r) ∨ t ≈O ∨ t ≈I ∨ ψ) w̲A'Tube w̲A'Base .comp O
