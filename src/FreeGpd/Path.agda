{-# OPTIONS --safe #-}
module FreeGpd.Path where

open import Prelude
open import Data.Star as Star
open import Data.Flip as Flip

open import RPath as RP
open import FreeGpd.Base as FG

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
      → FreeGpd G → Set (level-of-type V ⊔ ℓe)
R' {G} u =
  FG.rec
    hlevel!
    (λ v → el! (RPath G u v))
    (λ e → n-path $ ua (RPath-snoc-equiv {G = G} (fwd e))) -- could (should?) be done in the other direction

@0 R : {G : V → V → 𝒰 ℓe}
     → (u : V)
     → FreeGpd G → 𝒰 (level-of-type V ⊔ ℓe)
R u fg = R' u fg .n-Type.carrier

unfold : {x : V} → (y : V) → RPath G x y → vtx {G = G} x ＝ vtx y
unfold {G} y = RP.rec go
  where
  go : Rec λ a b → vtx {G = G} a ＝ vtx b
  go .εʳ = ap vtx
  go .◅~ʳ (fwd g) _ e = edge g ∙ e
  go .◅~ʳ (bwd g) _ e = edge g ⁻¹ ∙ e
  go .bwdfwdʳ gyx _ bxz = ∙-cancel-l (edge gyx) bxz
  go .fwdbwdʳ gxy _ bxz = ∙-cancel-l (edge gxy ⁻¹) bxz
  go .truncʳ = hlevel!

unfold-concat : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                {x y z : V} {rxy : RPath G x y} {ryz : RPath G y z}
              → unfold z (concat rxy ryz) ＝ unfold y rxy ∙ unfold z ryz
unfold-concat {G} {z} {rxy} {ryz} = RP.elim-prop go rxy ryz
  where
  go : Elim-prop {G = G} λ {x} {y} q → (ryz : RPath G y z)
                          → unfold z (concat q ryz) ＝ unfold y q ∙ unfold z ryz
  go .εʳ =
    Jₚ (λ w ew → (ryz : RPath G w z)
               → unfold z (concat (ε~ ew) ryz) ＝ unfold w (ε~ ew) ∙ₚ unfold z ryz)
       λ ryz' →   ap (unfold z) (concat-nil-l {r = ryz'})
                ∙ ∙-id-o (unfold z ryz') ⁻¹
  go .◅~ʳ (fwd fxy) {gyz} ih gwz =
      ap (edge fxy ∙_) (ih gwz)
    ∙ ∙-assoc (edge fxy) (unfold _ gyz) (unfold z gwz)
  go .◅~ʳ (bwd fyx) {gyz} ih gwz =
    ap (edge fyx ⁻¹ ∙_) (ih gwz)
    ∙ ∙-assoc (edge fyx ⁻¹) (unfold _ gyz) (unfold z gwz)
  go .truncʳ _ = hlevel!

unfold-fwd-snoc : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                 {x y z : V} {rxy : RPath G x y} {gyz : G y z}
               → unfold z (rxy ◅~+ fwd gyz) ＝ unfold y rxy ∙ edge gyz
unfold-fwd-snoc {G} {z} {rxy} {gyz} =
  unfold-concat {rxy = rxy} ∙ ap (unfold _ rxy ∙_) (∙-id-i (edge gyz))

unfold-bwd-snoc : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                 {x y z : V} {rxy : RPath G x y} {gzy : G z y}
               → unfold z (rxy ◅~+ bwd gzy) ＝ unfold y rxy ∙ edge gzy ⁻¹
unfold-bwd-snoc {G} {z} {rxy} {gzy} =
  unfold-concat {rxy = rxy} ∙ ap (unfold _ rxy ∙_) (∙-id-i (edge gzy ⁻¹))

@0 decode : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
          → {x : V} → (fg : FreeGpd G) → R x fg → vtx {G = G} x ＝ fg
decode {V} {G} {x} =
  elim-set hlevel! unfold aux
  where
  aux : {y z : V} (e : G y z)
      → ＜ unfold y ／ (λ i → R {G = G} x (edge e i) → vtx {G = G} x ＝ edge e i) ＼ unfold z ＞
  aux {z} e =
    fun-ext-dep λ {x₀} {x₁} p →
      commutes→square (  ∙-id-o (unfold z x₁)
                       ∙ ap (unfold z)
                            (from-pathᴾ p ⁻¹ ∙ ua-β (RPath-snoc-equiv (fwd e)) x₀)
                       ∙ unfold-fwd-snoc {rxy = x₀})

@0 encode' : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
          → (x : V) → {y : V} {fg : FreeGpd G} → vtx y ＝ fg → RPath G x y → R x fg
encode' x = subst (R x)

@0 encode : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
          → (x : V) → {fg : FreeGpd G} → vtx x ＝ fg → R x fg
encode x p = encode' x p nil

@0 encode'-decode-vtx : {x y z : V} (rxy : RPath G x y) (ryz : RPath G y z)
                      → encode' x (decode (vtx z) ryz) rxy ＝ concat rxy ryz
encode'-decode-vtx {G} {x} rxy ryz = RP.elim-prop go ryz rxy
  where
  go : Elim-prop {G = G} λ {x = y} {y = z} q
                         → (rxy : RPath G x y) → encode' x (decode (vtx z) q) rxy ＝ concat rxy q
  go .εʳ {x = y} {y = z} e rxy =
    Jₚ (λ w ew → encode' x (decode (vtx w) (ε~ ew)) rxy ＝ concat rxy (ε~ ew))
       (  subst-refl {B = RPath G _} rxy
        ∙ concat-nil-r ⁻¹)
       e
  go .◅~ʳ {x = y} {y = z} {z = w} (fwd fyz) {gyz = gzw} ih rxy =
      subst-comp (R x) (edge fyz) (unfold _ gzw) rxy
    ∙ ap (subst (R x) (unfold w gzw))
         (ua-β (RPath-snoc-equiv (fwd fyz)) rxy)
    ∙ ih (rxy ◅~+ fwd fyz)
    ∙ concat-assoc {rwx = rxy}
    ∙ ap (λ q → concat rxy (fwd fyz ◅~ q)) concat-nil-l
  go .◅~ʳ {x = y} {y = z} {z = w} (bwd fzy) {gyz = gzw} ih rxy =
      subst-comp (R x) (edge fzy ⁻¹) (unfold _ gzw) rxy
    ∙ ap (subst (R x) (unfold w gzw))
         (ua-β⁻¹ (RPath-snoc-equiv (fwd fzy)) rxy)
    ∙ ih (rxy ◅~+ bwd fzy)
    ∙ concat-assoc {rwx = rxy}
    ∙ ap (λ q → concat rxy (bwd fzy ◅~ q)) concat-nil-l
  go .truncʳ _ = hlevel!

@0 encode-decode-vtx : {x y : V} (r : RPath G x y)
                     → encode x (decode (vtx y) r) ＝ r
encode-decode-vtx {G} r = encode'-decode-vtx nil r ∙ concat-nil-l

@0 encode-decode : {x : V} {fg : FreeGpd G}
                   (r : R x fg) → encode x (decode fg r) ＝ r
encode-decode {x} {fg} =
 FG.elim-prop
   {C = λ q → (r : R x q) → encode x (decode q r) ＝ r}
   hlevel!
   (λ v → encode-decode-vtx)
   fg

@0 decode-encode : {x : V} {fg : FreeGpd G}
                   (eq : vtx x ＝ fg) → decode fg (encode x eq) ＝ eq
decode-encode {G} {x} {fg} =
  Jₚ (λ v ev → decode v (encode x ev) ＝ ev)
     (ap (unfold x)
         (subst-refl {B = R {G = G} x} {x = vtx x}
                     nil))

@0 FreeGpd-≃ : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
            → (x : V) → (fg : FreeGpd G) → vtx {G = G} x ＝ fg ≃ R x fg
FreeGpd-≃ x fg =
  ≅→≃ $
  make-iso (encode x) (decode fg) $
  make-inverses (fun-ext (encode-decode {fg = fg})) (fun-ext decode-encode)

@0 FreeGpd-≃' : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
              → {x y : V} → vtx {G = G} x ＝ vtx y ≃ RPath G x y
FreeGpd-≃' {x} {y} = FreeGpd-≃ x (vtx y)
