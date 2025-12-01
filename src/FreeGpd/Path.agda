{-# OPTIONS --safe #-}
module FreeGpd.Path where

open import Prelude
open import Data.Star
open import Data.Flip renaming (rec to recF)
open import Data.Quotient.Set as SetQ renaming ( elim to elimₛ ; elim-prop to elim-propₛ ; rec to recₛ
                                               ; encode to encodeₛ ; decode to decodeₛ)

open import RPath
open import FreeGpd.Base

private variable
  ℓv ℓe ℓ : Level
  V : 𝒰 ℓv
  A : 𝒰 ℓ
  G : V → V → 𝒰 ℓe

instance opaque
  H-Level-FreeGpd
    : ∀ {ℓv ℓe} {V : 𝒰 ℓv} {G : V → V → 𝒰 ℓe}
    → ∀ {n} → ⦃ n ≥ʰ 3 ⦄ → H-Level n (FreeGpd G)
  H-Level-FreeGpd ⦃ s≤ʰs (s≤ʰs (s≤ʰs _)) ⦄ = hlevel-basic-instance 3 trunc

-- encode-decode

@0 R' : {G : V → V → 𝒰 ℓe}
      → (u : V)
      → FreeGpd G → Set (level-of-type V ⊔ ℓsuc ℓe)
R' {G} u =
  rec
    hlevel!
    (λ v → el! (RPath G u v))
    (λ e → n-path $ ua (RPath-snoc-equiv {G = G} e)) -- could (should?) be done in the other direction

@0 R : {G : V → V → 𝒰 ℓe}
     → (u : V)
     → FreeGpd G → 𝒰 (level-of-type V ⊔ ℓsuc ℓe)
R u fg = R' u fg .n-Type.carrier

unfold' : {x y : V} → RSTClos G x y → vtx {G = G} x ＝ vtx y
unfold' = rstc-rec (ap vtx) edge _⁻¹ _∙_

unfold'-◅+f : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
              {x y z : V} {r : RSTClos G x y} {e : G y z}
            → unfold' (r ◅+f e) ＝ unfold' r ∙ edge e
unfold'-◅+f {G} {r} {e} =
  rstc-rec-◅+f {pl = _∙_}
    (∙-id-o _)
    (∙-id-i _)
    (∙-assoc _ _ _)
    r e

unfold'-◅+b : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
              {x y z : V} {r : RSTClos G x y} {e : G z y}
            → unfold' (r ◅+b e) ＝ unfold' r ∙ edge e ⁻¹
unfold'-◅+b {G} {r} {e} =
  rstc-rec-◅+b {pl = _∙_}
    (∙-id-o _)
    (∙-id-i _)
    (∙-assoc _ _ _)
    r e

unfold'-eqv : {x y : V} (a b : RSTClos G x y)
            → a ~ b → unfold' a ＝ unfold' b
unfold'-eqv a b (eqt eq)           = ap unfold' eq
unfold'-eqv a b (symt eqv)         = unfold'-eqv b a eqv ⁻¹
unfold'-eqv a b (transt eqv1 eqv2) = unfold'-eqv a _ eqv1 ∙ unfold'-eqv _ b eqv2
unfold'-eqv a b (congrf eqv)       = edge _ ◁ unfold'-eqv _ _ eqv
unfold'-eqv a b (congrb eqv)       = edge _ ⁻¹ ◁ unfold'-eqv _ _ eqv
unfold'-eqv a b fwdbwd             = ∙-cancel-l (edge _) (unfold' b)
unfold'-eqv a b bwdfwd             = ∙-cancel-l (edge _ ⁻¹) (unfold' b)
unfold'-eqv a b (prop eqv eqv2 i)  =
  trunc (vtx _) (vtx _)
        (unfold' a) (unfold' b)
        (unfold'-eqv a b eqv) (unfold'-eqv a b eqv2)
        i

unfold : {x : V} → (y : V) → RPath G x y → vtx {G = G} x ＝ vtx y
unfold y = recₛ hlevel! unfold' unfold'-eqv

unfold-fwdsnoc : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                 {x y z : V} {e : G y z} {r : RPath G x y}
               → unfold z (fwdsnoc e r) ＝ unfold y r ∙ edge e
unfold-fwdsnoc {y} {z} {e} {r} =
  elim-propₛ
    {P = λ q → unfold z (fwdsnoc e q) ＝ unfold y q ∙ edge e}
    hlevel!
    (λ r → unfold'-◅+f {r = r})
    r

unfold-bwdsnoc : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                 {x y z : V} {e : G z y} {r : RPath G x y}
               → unfold z (bwdsnoc e r) ＝ unfold y r ∙ edge e ⁻¹
unfold-bwdsnoc {y} {z} {e} {r} =
  elim-propₛ
    {P = λ q → unfold z (bwdsnoc e q) ＝ unfold y q ∙ edge e ⁻¹}
    hlevel!
    (λ r → unfold'-◅+b {r = r})
    r

@0 decode : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
          → (x : V) → (fg : FreeGpd G) → R x fg → vtx {G = G} x ＝ fg
decode {V} {G} x =
  elim-set hlevel! unfold aux
  where
  aux : {y z : V} (e : G y z)
      → ＜ unfold y ／ (λ i → R {G = G} x (edge e i) → vtx {G = G} x ＝ edge e i) ＼ unfold z ＞
  aux {z} e =
    fun-ext-dep λ {x₀} {x₁} p →
      commutes→square (  ∙-id-o (unfold z x₁)
                       ∙ ap (unfold z)
                            (from-pathᴾ p ⁻¹ ∙ ua-β (RPath-snoc-equiv e) x₀)
                       ∙ unfold-fwdsnoc {r = x₀})

@0 encode : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
          → (x : V) → (fg : FreeGpd G) → vtx x ＝ fg → R x fg
encode x _ p = subst (R x) p nil

@0 encode-decode-vtx : {x y : V} (r : RPath G x y)
                     → encode x (vtx y) (decode x (vtx y) r) ＝ r
encode-decode-vtx {G} {x} {y} =
  elim-propₛ
    {P = λ q → encode x (vtx y) (decode x (vtx y) q) ＝ q}
    hlevel!
    λ q → aux refl q ∙ ap ⦋_⦌ (star-cast-l-refl q)
  where
  aux : ∀ {a b c}
      → (w : RSTClos G a b) (q : RSTClos G b c)
      → subst (R a) (unfold' q) ⦋ w ⦌ ＝ ⦋ w ∙ q ⦌
  aux     w (ε eq)      =
    ap ⦋_⦌ (Jₚ (λ z ez → subst (RSTClos _ _) ez w ＝ w ∙ ε ez)
              (subst-refl {B = RSTClos _ _} w ∙ star-trans-id-r w ⁻¹)
              eq)
  aux {a} w (fwd e ◅ q) =
      subst-comp (R a) (edge e) (unfold' q) ⦋ w ⦌
    ∙ ap (subst (R a) (unfold' q))
         (ua-β (RPath-snoc-equiv e) ⦋ w ⦌)
    ∙ aux (w ◅+f e) q
    ∙ ap ⦋_⦌ (  star-trans-assoc w (star-sng (fwd e)) q
             ∙ ap (λ q → w ∙ (fwd e ◅ q))
                  (star-trans-id-l q))
  aux {a} w (bwd e ◅ q) =
      subst-comp (R a) (edge e ⁻¹) (unfold' q) ⦋ w ⦌
    ∙ ap (subst (R a) (unfold' q))
         (ua-β⁻¹ (RPath-snoc-equiv e) ⦋ w ⦌)
    ∙ aux (w ◅+b e) q
    ∙ ap ⦋_⦌ (  star-trans-assoc w (star-sng (bwd e)) q
             ∙ ap (λ q → w ∙ (bwd e ◅ q))
                  (star-trans-id-l q))

@0 encode-decode : {x : V} {fg : FreeGpd G}
                   (r : R x fg) → encode x fg (decode x fg r) ＝ r
encode-decode {x} {fg} =
 elim-prop
   {C = λ q → (r : R x q) → encode x q (decode x q r) ＝ r}
   hlevel!
   (λ v → encode-decode-vtx)
   fg

@0 decode-encode : {x : V} {fg : FreeGpd G}
                   (eq : vtx x ＝ fg) → decode x fg (encode x fg eq) ＝ eq
decode-encode {G} {x} {fg} eq =
  J! (λ q pq → decode x q (encode x q pq) ＝ pq)
     (ap (unfold x)
         (subst-refl {B = R {G = G} x} {x = vtx x}
                     nil))
     eq

@0 FreeGpd-≃ : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
            → (x : V) → (fg : FreeGpd G) → vtx {G = G} x ＝ fg ≃ R x fg
FreeGpd-≃ x fg =
  ≅→≃ $
  make-iso (encode x fg) (decode x fg) $
  make-inverses (fun-ext (encode-decode {fg = fg})) (fun-ext decode-encode)

@0 FreeGpd-≃' : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
              → {x y : V} → vtx {G = G} x ＝ vtx y ≃ RPath G x y
FreeGpd-≃' {x} {y} = FreeGpd-≃ x (vtx y)
