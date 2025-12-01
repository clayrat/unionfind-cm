{-# OPTIONS --safe #-}
module RPath where

open import Prelude
open import Logic.Equivalence
open import Data.Reflects.Base as Reflects
open import Data.Star
open import Data.Flip renaming (rec to recF)
open import Data.Quotient.Set as SetQ renaming ( elim to elimₛ ; elim-prop to elim-propₛ ; rec to recₛ
                                               ; encode to encodeₛ ; decode to decodeₛ)

private variable
  ℓv ℓe ℓ : Level
  V : 𝒰 ℓv
  A : 𝒰 ℓ
  G : V → V → 𝒰 ℓe

-- reflexive-symmetric-transitive (equivalence) closure
-- = a type of bidirectional (aka chaotic) paths on a graph
RSTClos : ∀ {ℓᵃ ℓ} {A : 𝒰 ℓᵃ}
        → (A → A → 𝒰 ℓ)
        → A → A → 𝒰 (ℓᵃ ⊔ ℓ)
RSTClos = Star ∘ Flip

-- TODO use more symbols

_◅+f_ : ∀ {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ} {x y z : A}
      → RSTClos R x y → R y z → RSTClos R x z
r ◅+f e = r ◅+ fwd e

_◅+b_ : ∀ {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ} {x y z : A}
      → RSTClos R x y → R z y → RSTClos R x z
r ◅+b e = r ◅+ bwd e

rstc-rec : ∀ {ℓᵃ ℓ ℓ′} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ} {S : A → A → 𝒰 ℓ′}
         → (∀ {x y} → x ＝ y → S x y)
         → (∀ {x y} → R x y → S x y)
         → (∀ {x y} → S x y → S y x)
         → (∀ {x y z} → S x y → S y z → S x z)
         → ∀ {x y} → RSTClos R x y → S x y
rstc-rec re mp sy pl = star-foldrm re (recF mp sy) pl

rstc-rec-◅+f : ∀ {ℓᵃ ℓ ℓ′} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ} {S : A → A → 𝒰 ℓ′}
             → {re : ∀ {x y} → x ＝ y → S x y}
             → {mp : ∀ {x y} → R x y → S x y}
             → {sy : ∀ {x y} → S x y → S y x}
             → {pl : ∀ {x y z} → S x y → S y z → S x z}
             → (∀ {x y} {s : S x y} → pl (re refl) s ＝ s)
             → (∀ {x y} {s : S x y} → pl s (re refl) ＝ s)
             → (∀ {x y z w} {a : S x y} {b : S y z} {c : S z w} → pl a (pl b c) ＝ pl (pl a b) c)
             → ∀ {x y z} → (rxy : RSTClos R x y) (eyz : R y z)
             → rstc-rec re mp sy pl (rxy ◅+f eyz) ＝
               pl (rstc-rec re mp sy pl rxy) (mp eyz)
rstc-rec-◅+f {re} {mp} {sy} {pl} pllu plru plas rxy =
  star-foldrm-◅+ re (recF mp sy) pl pllu plru plas rxy ∘ fwd

rstc-rec-◅+b : ∀ {ℓᵃ ℓ ℓ′} {A : 𝒰 ℓᵃ} {R : A → A → 𝒰 ℓ} {S : A → A → 𝒰 ℓ′}
             → {re : ∀ {x y} → x ＝ y → S x y}
             → {mp : ∀ {x y} → R x y → S x y}
             → {sy : ∀ {x y} → S x y → S y x}
             → {pl : ∀ {x y z} → S x y → S y z → S x z}
             → (∀ {x y} {s : S x y} → pl (re refl) s ＝ s)
             → (∀ {x y} {s : S x y} → pl s (re refl) ＝ s)
             → (∀ {x y z w} {a : S x y} {b : S y z} {c : S z w} → pl a (pl b c) ＝ pl (pl a b) c)
             → ∀ {x y z} → (rxy : RSTClos R x y) (ezy : R z y)
             → rstc-rec re mp sy pl (rxy ◅+b ezy) ＝
               pl (rstc-rec re mp sy pl rxy) (sy (mp ezy))
rstc-rec-◅+b {re} {mp} {sy} {pl} pllu plru plas rxy =
  star-foldrm-◅+ re (recF mp sy) pl pllu plru plas rxy ∘ bwd

-- quotiented RST closure (reduced paths on a graph)
data _~_ {G : V → V → 𝒰 ℓe} {x y : V} :
         RSTClos G x y → RSTClos G x y → 𝒰 (level-of-type V ⊔ ℓsuc ℓe) where
  eqt    : ∀ {rx ry} → rx ＝ ry → rx ~ ry
  symt   : ∀ {rx ry} → rx ~ ry → ry ~ rx
  transt : ∀ {rx ry rz} → rx ~ ry → ry ~ rz → rx ~ rz
  congrf : ∀ {z} {e : G x z} {r1 r2 : RSTClos G z y} → r1 ~ r2 → (fwd e ◅ r1) ~ (fwd e ◅ r2)
  congrb : ∀ {z} {e : G z x} {r1 r2 : RSTClos G z y} → r1 ~ r2 → (bwd e ◅ r1) ~ (bwd e ◅ r2)
  -- the necessary part
  fwdbwd : ∀ {z : V} {e : G z x} {r : RSTClos G x y} → (bwd e ◅ (fwd e ◅ r)) ~ r
  bwdfwd : ∀ {z : V} {e : G x z} {r : RSTClos G x y} → (fwd e ◅ (bwd e ◅ r)) ~ r
  prop   : ∀ {r1 r2 : RSTClos G x y} → (p q : r1 ~ r2) → p ＝ q

instance
  ~-is-congruence : {x y : V} → is-congruence (_~_ {G = G} {x = x} {y = y})
  ~-is-congruence .is-congruence.equivalence .Equivalence.reflexive .Refl.refl = eqt refl
  ~-is-congruence .is-congruence.equivalence .Equivalence.symmetric Dual.ᵒᵖ = symt
  ~-is-congruence .is-congruence.equivalence .Equivalence.transitive .Comp._∙_ = transt
  ~-is-congruence .is-congruence.has-prop = prop

RPath : (V → V → 𝒰 ℓe) → V → V → 𝒰 (level-of-type V ⊔ ℓsuc ℓe)
RPath G x y = RSTClos G x y / _~_

nil : ∀ {x} → RPath G x x
nil = ⦋ ε refl ⦌

-- operations

congrf-snoc : ∀ {x y z} {e : G z y} {r1 r2 : RSTClos G x z}
            → r1 ~ r2 → (r1 ◅+f e) ~ (r2 ◅+f e)
congrf-snoc (eqt eq)           = eqt (ap (_◅+ _) eq)
congrf-snoc (symt eqv)         = symt (congrf-snoc eqv)
congrf-snoc (transt eqv1 eqv2) = transt (congrf-snoc eqv1) (congrf-snoc eqv2)
congrf-snoc (congrf eqv)       = congrf (congrf-snoc eqv)
congrf-snoc (congrb eqv)       = congrb (congrf-snoc eqv)
congrf-snoc  fwdbwd            = fwdbwd
congrf-snoc  bwdfwd            = bwdfwd
congrf-snoc (prop eqv1 eqv2 i) = prop (congrf-snoc eqv1) (congrf-snoc eqv2) i

congrb-snoc : ∀ {x y z} {e : G y z} {r1 r2 : RSTClos G x z}
            → r1 ~ r2 → (r1 ◅+b e) ~ (r2 ◅+b e)
congrb-snoc (eqt eq)           = eqt (ap (_◅+b _) eq)
congrb-snoc (symt eqv)         = symt (congrb-snoc eqv)
congrb-snoc (transt eqv1 eqv2) = transt (congrb-snoc eqv1) (congrb-snoc eqv2)
congrb-snoc (congrf eqv)       = congrf (congrb-snoc eqv)
congrb-snoc (congrb eqv)       = congrb (congrb-snoc eqv)
congrb-snoc  fwdbwd            = fwdbwd
congrb-snoc  bwdfwd            = bwdfwd
congrb-snoc (prop eqv1 eqv2 i) = prop (congrb-snoc eqv1) (congrb-snoc eqv2) i

congr-trans-l : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                {x y z : V} {r : RSTClos G x y} {r1 r2 : RSTClos G y z}
              → r1 ~ r2 → r ∙ r1 ~ r ∙ r2
congr-trans-l {r = ε eq} {r1} {r2}     =
  Jₚ (λ a ea → (r1' r2' : RSTClos _ a _) → r1' ~ r2'
             → star-cast-l (ea ⁻¹) r1' ~ star-cast-l (ea ⁻¹) r2')
     (λ r1' r2' eqv →
         transt (eqt (star-cast-l-refl r1'))
           (transt eqv
              (eqt (star-cast-l-refl r2' ⁻¹))))
     eq r1 r2
congr-trans-l {r = fwd x ◅ r}          eqv = congrf (congr-trans-l {r = r} eqv)
congr-trans-l {r = bwd x ◅ r}          eqv = congrb (congr-trans-l {r = r} eqv)

congr-trans-r : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                {x y z : V} {r1 r2 : RSTClos G x y} {r : RSTClos G y z}
              → r1 ~ r2 → r1 ∙ r ~ r2 ∙ r
congr-trans-r {r1} {r2} {r = ε eq}                   =
    Jₚ (λ a ea → (r1' r2' : RSTClos _ _ _) → r1' ~ r2'
               → star-trans r1' (ε ea) ~ star-trans r2' (ε ea))
     (λ r1' r2' eqv →
         transt (eqt (star-trans-id-r r1'))
           (transt eqv
             (eqt (star-trans-id-r r2' ⁻¹))))
     eq r1 r2
congr-trans-r {r1} {r2} {r = fwd e ◅ r}          eqv =
  transt
    (eqt (  ap (star-trans r1) (star-trans-sng (fwd e) r)
          ∙ star-trans-assoc r1 (star-sng (fwd e)) r ⁻¹))
    (transt
       (congr-trans-r (congrf-snoc eqv))
       (eqt (  star-trans-assoc r2 (star-sng (fwd e)) r
             ∙ ap (star-trans r2) (star-trans-sng (fwd e) r ⁻¹))))
congr-trans-r {r1} {r2} {r = bwd e ◅ r}          eqv =
  transt
    (eqt (  ap (star-trans r1) (star-trans-sng (bwd e) r)
          ∙ star-trans-assoc r1 (star-sng (bwd e)) r ⁻¹))
    (transt
       (congr-trans-r (congrb-snoc eqv))
       (eqt (  star-trans-assoc r2 (star-sng (bwd e)) r
             ∙ ap (star-trans r2) (star-trans-sng (bwd e) r ⁻¹))))

bwdfwd-snoc : ∀ {x y z : V} {e : G z y} {r : RSTClos G x y}
            → ((r ◅+b e) ◅+f e) ~ r
bwdfwd-snoc {e} {r} =
  transt
    (eqt ((star-trans-assoc r (star-sng $ bwd e) (star-sng $ fwd e))))
    (transt
       (congr-trans-l {r = r} $
        transt (congrb (eqt (star-cast-l-refl (star-sng $ fwd e))))
               fwdbwd)
       (eqt (star-trans-id-r r)))

fwdbwd-snoc : ∀ {x y z : V} {e : G y z} {r : RSTClos G x y}
            → ((r ◅+f e) ◅+b e) ~ r
fwdbwd-snoc {e} {r} =
  transt
    (eqt ((star-trans-assoc r (star-sng $ fwd e) (star-sng $ bwd e))))
    (transt
       (congr-trans-l {r = r} $
        transt (congrf (eqt (star-cast-l-refl (star-sng $ bwd e))))
               bwdfwd)
       (eqt (star-trans-id-r r)))

-- TODO use more symbols

fwdcons : ∀ {x y z}
        → G x y → RPath G y z → RPath G x z
fwdcons e =
  recₛ (hlevel 2)
    (λ q → ⦋ fwd e ◅ q ⦌)
    λ a b ab → glue/ (fwd e ◅ a) (fwd e ◅ b)
                     (congrf ab)

bwdcons : ∀ {x y z}
        → G x y → RPath G x z → RPath G y z
bwdcons e =
  recₛ (hlevel 2)
    (λ q → ⦋ bwd e ◅ q ⦌)
    λ a b ab → glue/ (bwd e ◅ a) (bwd e ◅ b)
                     (congrb ab)

fwdsnoc : ∀ {x y z}
        → G y z → RPath G x y → RPath G x z
fwdsnoc e =
  recₛ (hlevel 2)
    (λ q → ⦋ q ◅+f e ⦌)
    λ a b ab → glue/ (a ◅+f e) (b ◅+f e)
                     (congrf-snoc ab)

bwdsnoc : ∀ {x y z}
        → G y z → RPath G x z → RPath G x y
bwdsnoc e =
  recₛ (hlevel 2)
    (λ q → ⦋ q ◅+ bwd e ⦌)
    λ a b ab → glue/ (a ◅+b e) (b ◅+b e)
                      (congrb-snoc ab)

fwdbwdcons : ∀ {x y z}
           → (e : G y x) → (ryz : RPath G y z)
           → fwdcons e (bwdcons e ryz) ＝ ryz
fwdbwdcons e =
  elim-propₛ hlevel!
    (λ q → glue/ (fwd e ◅ (bwd e ◅ q)) q bwdfwd)

bwdfwdcons : ∀ {x y z}
           → (e : G x y) → (ryz : RPath G y z)
           → bwdcons e (fwdcons e ryz) ＝ ryz
bwdfwdcons e =
  elim-propₛ hlevel!
    (λ q → glue/ (bwd e ◅ (fwd e ◅ q)) q fwdbwd)

fwdbwdsnoc : ∀ {x y z}
           → (e : G y z) → (rxz : RPath G x z)
           → fwdsnoc e (bwdsnoc e rxz) ＝ rxz
fwdbwdsnoc e =
  elim-propₛ hlevel!
    (λ q → glue/ ((q ◅+b e) ◅+f e) q bwdfwd-snoc)

bwdfwdsnoc : ∀ {x y z}
           → (e : G y z) → (rxy : RPath G x y)
           → bwdsnoc e (fwdsnoc e rxy) ＝ rxy
bwdfwdsnoc e =
  elim-propₛ hlevel!
    (λ q → glue/ ((q ◅+f e) ◅+b e) q fwdbwd-snoc)

fwdcons-equiv : {x y z : V}
              → (e : G x y) → is-equiv (fwdcons {G = G} {z = z} e)
fwdcons-equiv e =
  qinv→is-equiv $ qinv (bwdcons e) (fun-ext $ fwdbwdcons e) (fun-ext $ bwdfwdcons e)

fwdsnoc-equiv : {x y z : V}
              → (e : G y z) → is-equiv (fwdsnoc {G = G} {x = x} e)
fwdsnoc-equiv e =
  qinv→is-equiv $ qinv (bwdsnoc e) (fun-ext $ fwdbwdsnoc e) (fun-ext $ bwdfwdsnoc e)

RPath-cons-equiv : ∀ {x y z}
                 → G x y → RPath G y z ≃ RPath G x z
RPath-cons-equiv e = fwdcons e , fwdcons-equiv e

RPath-snoc-equiv : ∀ {x y z}
                 → G y z → RPath G x y ≃ RPath G x z
RPath-snoc-equiv e = fwdsnoc e , fwdsnoc-equiv e

concat : {x y z : V}
       → RPath G x y → RPath G y z → RPath G x z
concat =
  rec² (hlevel 2)
    (λ xy yz → ⦋ xy ∙ yz ⦌)
    (λ xy1 xy2 yz → glue/ _ _ ∘ congr-trans-r)
    λ xy yz1 yz2 → glue/ _ _ ∘ congr-trans-l {r = xy}

-- TODO map/foldr?

-- properties

is-connected-graph : (V → V → 𝒰 ℓe) → 𝒰 (level-of-type V ⊔ ℓsuc ℓe)
is-connected-graph G = ∀ x y → RPath G x y

-- ≈ is a forest
is-circuit-free : (V → V → 𝒰 ℓe) → 𝒰 (level-of-type V ⊔ ℓsuc ℓe)
is-circuit-free {V} G = (x : V) → (r : RPath G x x) → r ＝ nil
