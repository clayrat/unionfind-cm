{-# OPTIONS --safe #-}
module RPath where

open import Prelude
open import Logic.Equivalence
open import Data.Reflects.Base as Reflects
open import Data.Star as Star renaming (elim to elimˢ ; rec to recˢ)
open import Data.Flip as Flip renaming (elim to elimᶠ ; rec to recᶠ)

private variable
  ℓv ℓe ℓ ℓ′ : Level
  V : 𝒰 ℓv
  A : 𝒰 ℓ
  G : V → V → 𝒰 ℓe

data RPath (G : V → V → 𝒰 ℓe) : V → V → 𝒰 (level-of-type V ⊔ ℓe) where
  ε~     : ∀ {x y} → x ＝ y → RPath G x y
  _◅~_   : ∀ {x y z} → Flip G x y → RPath G y z → RPath G x z
  bwdfwd : ∀ {x y z} {gyx : G y x} {rxz : RPath G x z} → bwd gyx ◅~ (fwd gyx ◅~ rxz) ＝ rxz
  fwdbwd : ∀ {x y z} {gxy : G x y} {rxz : RPath G x z} → fwd gxy ◅~ (bwd gxy ◅~ rxz) ＝ rxz
  trunc  : ∀ {x y} → is-set (RPath G x y)

instance opaque
  H-Level-RPath : ∀ {n x y} → ⦃ n ≥ʰ 2 ⦄ → H-Level n (RPath G x y)
  H-Level-RPath ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 trunc
  {-# OVERLAPPING H-Level-RPath #-}

-- eliminators

record Elim {G : V → V → 𝒰 ℓe} (P : ∀ {x y} → RPath G x y → 𝒰 ℓ′) : 𝒰 (level-of-type V ⊔ ℓe ⊔ ℓ′) where
  no-eta-equality
  field
    εʳ      : {x y : V} → (e : x ＝ y) → P (ε~ e)
    ◅~ʳ     : {x y z : V} → (f : Flip G x y) → {r : RPath G y z} → P r → P (f ◅~ r)
    bwdfwdʳ : ∀ {x y z} {gyx : G y x} {rxz : RPath G x z} (p : P rxz)
            → ＜ ◅~ʳ (bwd gyx) (◅~ʳ (fwd gyx) p) ／ (λ i → P (bwdfwd {gyx = gyx} {rxz = rxz} i)) ＼ p ＞
    fwdbwdʳ : ∀ {x y z} {gxy : G x y} {rxz : RPath G x z} (p : P rxz)
            → ＜ ◅~ʳ (fwd gxy) (◅~ʳ (bwd gxy) p) ／ (λ i → P (fwdbwd {gxy = gxy} {rxz = rxz} i)) ＼ p ＞
    truncʳ : ∀ {x y} (r : RPath G x y) → is-set (P r)

open Elim public

elim : {P : ∀ {x y} → RPath G x y → 𝒰 ℓ′} → Elim P
     → {x y : V} → (r : RPath G x y) → P r
elim {V} {G} {P} e = go
  where
  module E = Elim e
  go : {a b : V} → (r : RPath G a b) → P r
  go (ε~ eq) = E.εʳ eq
  go (f ◅~ r) = E.◅~ʳ f (go r)
  go (bwdfwd {rxz} i) = E.bwdfwdʳ (go rxz) i
  go (fwdbwd {rxz} i) = E.fwdbwdʳ (go rxz) i
  go (trunc r₁ r₂ e₁ e₂ i j) =
    is-set→squareᴾ
      (λ i₁ j₁ → E.truncʳ (trunc r₁ r₂ e₁ e₂ i₁ j₁))
      refl
      (λ k → go (e₁ k))
      (λ k → go (e₂ k))
      refl
      i j

record Elim-prop {G : V → V → 𝒰 ℓe} (P : ∀ {x y} → RPath G x y → 𝒰 ℓ′) : 𝒰 (level-of-type V ⊔ ℓe ⊔ ℓ′) where
  no-eta-equality
  field
    εʳ      : {x y : V} → (e : x ＝ y) → P (ε~ e)
    ◅~ʳ     : {x y z : V} → (fxy : Flip G x y) → {gyz : RPath G y z} → P gyz → P (fxy ◅~ gyz)
    truncʳ : ∀ {x y} (r : RPath G x y) → is-prop (P r)

open Elim-prop public

elim-prop : {P : ∀ {x y} → RPath G x y → 𝒰 ℓ′} → Elim-prop P
          → {x y : V} → (r : RPath G x y) → P r
elim-prop {P} e = elim e′
  where
  module E = Elim-prop e

  e′ : Elim P
  e′ .εʳ = E.εʳ
  e′ .◅~ʳ = E.◅~ʳ
  e′ .bwdfwdʳ {gyx} p = to-pathᴾ (E.truncʳ (bwdfwd {gyx = gyx} i1) _ p)
  e′ .fwdbwdʳ {gxy} p = to-pathᴾ (E.truncʳ (fwdbwd {gxy = gxy} i1) _ p)
  e′ .truncʳ p = is-of-hlevel-suc 1 $ E.truncʳ p

-- TODO elim-propJ

record Rec {G : V → V → 𝒰 ℓe} (B : V → V → 𝒰 ℓ′) : 𝒰 (level-of-type V ⊔ ℓe ⊔ ℓ′) where
  no-eta-equality
  field
    εʳ      : ∀ {x y} → x ＝ y → B x y
    ◅~ʳ     : ∀ {x y z} → Flip G x y → RPath G y z → B y z → B x z
    bwdfwdʳ : ∀ {x y z} (gyx : G y x) (rxz : RPath G x z) (bxz : B x z)
            → ◅~ʳ (bwd gyx) (fwd gyx ◅~ rxz) (◅~ʳ (fwd gyx) rxz bxz) ＝ bxz
    fwdbwdʳ : ∀ {x y z} (gxy : G x y) (rxz : RPath G x z) (bxz : B x z)
            → ◅~ʳ (fwd gxy) (bwd gxy ◅~ rxz) (◅~ʳ (bwd gxy) rxz bxz) ＝ bxz
    truncʳ : ∀ {x y} → is-set (B x y)

open Rec public

rec : {B : V → V → 𝒰 ℓ′}
    → Rec {G = G} B → {x y : V} → RPath G x y → B x y
rec {B} r = elim go
  where
  module R = Rec r
  go : Elim (λ {x} {y} _  → B x y)
  go .εʳ = R.εʳ
  go .◅~ʳ f {r} = R.◅~ʳ f r
  go .bwdfwdʳ {gyx} {rxz} = R.bwdfwdʳ gyx rxz
  go .fwdbwdʳ {gxy} {rxz} = R.fwdbwdʳ gxy rxz
  go .truncʳ _ = R.truncʳ

-- operations

nil : ∀ {x} → RPath G x x
nil = ε~ refl

sng : ∀ {x y} → Flip G x y → RPath G x y
sng f = f ◅~ nil

concat : ∀ {x y z} → RPath G x y → RPath G y z → RPath G x z
concat {G} {x} {y} {z} = rec go
  where
  go : Rec {G = G} (λ a b → RPath G b z → RPath G a z)
  go .εʳ e f = subst (λ q → RPath G q z) (e ⁻¹) f
  go .◅~ʳ f r rr r2 = f ◅~ rr r2
  go .bwdfwdʳ gyx rxz rr = fun-ext λ b → bwdfwd
  go .fwdbwdʳ gxy rxz rr = fun-ext λ b → fwdbwd
  go .truncʳ = hlevel!

-- snoc
_◅~+_ : ∀ {x y z} → RPath G x y → Flip G y z → RPath G x z
_◅~+_ r = concat r ∘ sng

embed : {x y : V} → Star G x y → RPath G x y
embed = Star.rec ε~ λ e → fwd e ◅~_

mirror : {x y : V} → Star G y x → RPath G x y
mirror = Star.rec (ε~ ∘ _⁻¹) λ e → _◅~+ bwd e

-- TODO map/foldr?

-- properties

concat-nil-l : ∀ {x y} {r : RPath G x y}
             → concat nil r ＝ r
concat-nil-l {x} {y} {r} =
  subst-refl {B = λ q → RPath _ q _} r

concat-nil-r : ∀ {x y} {r : RPath G x y}
             → concat r nil ＝ r
concat-nil-r {r} = elim-prop go r
  where
  go : Elim-prop λ {x} {y} q → concat q nil ＝ q
  go .εʳ e = Jₚ (λ v e → concat (ε~ e) nil ＝ ε~ e) concat-nil-l e
  go .◅~ʳ f ih = ap (f ◅~_) ih
  go .truncʳ = hlevel!

concat-sng-l : ∀ {x y z} {fxy : Flip G x y} {ryz : RPath G y z}
             → concat (sng fxy) ryz ＝ fxy ◅~ ryz
concat-sng-l {fxy} = ap (fxy ◅~_) concat-nil-l

concat-assoc : ∀ {w x y z} {rwx : RPath G w x} {rxy : RPath G x y} {ryz : RPath G y z}
             → concat (concat rwx rxy) ryz ＝ concat rwx (concat rxy ryz)
concat-assoc {G} {y} {z} {rwx} {rxy} {ryz} = elim-prop go rwx rxy ryz
  where
  go : Elim-prop λ {x = w} {y = x} q
                 → (rxy : RPath G x y) → (ryz : RPath G y z)
                 → concat (concat q rxy) ryz ＝ concat q (concat rxy ryz)
  go .εʳ e rxy ryz =
    Jₚ (λ v ev → (rxy : RPath G v y)
                → concat (concat (ε~ ev) rxy) ryz ＝ concat (ε~ ev) (concat rxy ryz))
       (λ rxy' →   ap (λ q → concat q ryz) (concat-nil-l {r = rxy'})
                  ∙ concat-nil-l ⁻¹)
        e rxy
  go .◅~ʳ fxy ih rxy ryz = ap (fxy ◅~_) (ih rxy ryz)
  go .truncʳ _ = hlevel!


bwdfwd-snoc : {V : 𝒰 ℓv} {G : V → V → 𝒰 ℓe}
              {x y z : V}
            → {g : G y z} {r : RPath G x y}
            → ((r ◅~+ fwd g) ◅~+ bwd g) ＝ r
bwdfwd-snoc {g} {r} =
    concat-assoc {rwx = r} {rxy = sng (fwd g)}
  ∙ ap (concat r) (ap (fwd g ◅~_) concat-nil-l ∙ fwdbwd)
  ∙ concat-nil-r

fwdbwd-snoc : {V : 𝒰 ℓv} {G : V → V → 𝒰 ℓe}
              {x y z : V}
            → {g : G z y} {r : RPath G x y}
            → ((r ◅~+ bwd g) ◅~+ fwd g) ＝ r
fwdbwd-snoc {g} {r} =
    concat-assoc {rwx = r} {rxy = sng (bwd g)}
  ∙ ap (concat r) (ap (bwd g ◅~_) concat-nil-l ∙ bwdfwd)
  ∙ concat-nil-r

-- TODO leave just one of each and use involutiveness?
invert-l-eq : {V : 𝒰 ℓv} {G : V → V → 𝒰 ℓe}
              {x y z : V}
            → {f : Flip G y x} {r : RPath G x z}
            → (f ⁻¹ ◅~ (f ◅~ r)) ＝ r
invert-l-eq {f = fwd x} = bwdfwd
invert-l-eq {f = bwd x} = fwdbwd

invert-r-eq : {V : 𝒰 ℓv} {G : V → V → 𝒰 ℓe}
              {x y z : V}
            → {f : Flip G x y} {r : RPath G x z}
            → (f ◅~ (f ⁻¹ ◅~ r)) ＝ r
invert-r-eq {f = fwd x} = fwdbwd
invert-r-eq {f = bwd x} = bwdfwd

invert-snoc-l-eq : {V : 𝒰 ℓv} {G : V → V → 𝒰 ℓe}
                   {x y z : V}
                 → {f : Flip G z y} {r : RPath G x y}
                 → ((r ◅~+ f ⁻¹) ◅~+ f) ＝ r
invert-snoc-l-eq {f = fwd x} = fwdbwd-snoc
invert-snoc-l-eq {f = bwd x} = bwdfwd-snoc

invert-snoc-r-eq : {V : 𝒰 ℓv} {G : V → V → 𝒰 ℓe}
                   {x y z : V}
                 → {f : Flip G y z} {r : RPath G x y}
                 → ((r ◅~+ f) ◅~+ f ⁻¹) ＝ r
invert-snoc-r-eq {f = fwd x} = bwdfwd-snoc
invert-snoc-r-eq {f = bwd x} = fwdbwd-snoc

cons-equiv : {x y z : V}
           → (f : Flip G x y) → is-equiv (_◅~_ {z = z} f)
cons-equiv f =
  qinv→is-equiv $
  qinv (f ⁻¹ ◅~_)
    (fun-ext λ _ → invert-r-eq)
    (fun-ext λ _ → invert-l-eq)

snoc-equiv : {x y z : V}
           → (f : Flip G y z) → is-equiv (λ r → _◅~+_ {x = x} r f)
snoc-equiv f =
  qinv→is-equiv $
  qinv (λ r → r ◅~+ (f ⁻¹))
    (fun-ext λ _ → invert-snoc-l-eq)
    (fun-ext λ _ → invert-snoc-r-eq)

-- TODO concat-l-equiv / concat-r-equiv

RPath-cons-equiv : ∀ {x y z}
                 → Flip G x y → RPath G y z ≃ RPath G x z
RPath-cons-equiv e = e ◅~_ , cons-equiv e

RPath-snoc-equiv : ∀ {x y z}
                 → Flip G y z → RPath G x y ≃ RPath G x z
RPath-snoc-equiv e = _◅~+ e , snoc-equiv e

embed-snoc : ∀ {x y z} (sxy : Star G x y) (gyz : G y z)
           → embed (sxy ◅+ gyz) ＝ embed sxy ◅~+ fwd gyz
embed-snoc {G} {z} =
  elimJ {P = λ {x} {y} q → (gyz : G y z)
               → embed (q ◅+ gyz) ＝ embed q ◅~+ fwd gyz}
    (λ gyz →   ap embed (star-trans-id-l (star-sng gyz))
             ∙ concat-nil-l ⁻¹)
    λ rxy ih gyz → ap (fwd rxy ◅~_) (ih gyz)

mirror-cons : ∀ {x y z} (gxy : G x y) (syz : Star G y z)
            → mirror (gxy ◅ syz) ＝ mirror syz ◅~+ bwd gxy
mirror-cons _ _ = refl

mirror-snoc : ∀ {x y z} (sxy : Star G x y) (gyz : G y z)
            → mirror (sxy ◅+ gyz) ＝ bwd gyz ◅~ mirror sxy
mirror-snoc {G} {z} =
  elimJ {P = λ {x} {y} q → (gyz : G y z)
               → mirror (q ◅+ gyz) ＝ bwd gyz ◅~ mirror q}
    (λ gxz → ap mirror (star-trans-id-l (star-sng gxz)) ∙ concat-nil-l)
    λ rxy {syz} ih gyz → ap (_◅~+ bwd rxy) (ih gyz)

concat-embed-mirror : ∀ {x y : V} (sxy : Star G x y)
                    → concat (embed sxy) (mirror sxy) ＝ nil
concat-embed-mirror =
  elim-◅+J
    {P = λ q → concat (embed q) (mirror q) ＝ nil}
    concat-nil-l
    λ sxy ih ryz →
        ap² concat (embed-snoc sxy ryz) (mirror-snoc sxy ryz)
      ∙ concat-assoc {rwx = embed sxy} {rxy = sng (fwd ryz)} {ryz = bwd ryz ◅~ mirror sxy}
      ∙ ap (concat (embed sxy)) (concat-sng-l ∙ fwdbwd)
      ∙ ih

-- graph/path properties

is-connected-graph : (V → V → 𝒰 ℓe) → 𝒰 (level-of-type V ⊔ ℓe)
is-connected-graph G = ∀ x y → RPath G x y

-- ≈ is a forest
is-circuit-free : (V → V → 𝒰 ℓe) → 𝒰 (level-of-type V ⊔ ℓe)
is-circuit-free {V} G = (x : V) → (r : RPath G x x) → r ＝ nil

-- reduced path which looks like this after normalization: x ----> z <---- y
is-cospan : {G : V → V → 𝒰 ℓe} {x y : V}
          → RPath G x y → 𝒰 (level-of-type V ⊔ ℓe)
is-cospan {V} {G} {x} {y} r =
  Σ[ z ꞉ V ] Σ[ f ꞉ Star G x z ] Σ[ b ꞉ Star G y z ] (r ＝ concat (embed f) (mirror b))
