{-# OPTIONS --safe #-}
module FreeGpd.Properties where

open import Prelude
open import Homotopy.Connectedness

open import Data.Star
open import Data.Quotient.Set as SetQ renaming ( elim to elimₛ ; elim-prop to elim-propₛ ; rec to recₛ
                                               ; encode to encodeₛ ; decode to decodeₛ ; universal to universalₛ )

open import RPath
open import FreeGpd.Base as FG
open import FreeGpd.Path

private variable
  ℓv ℓe ℓ : Level
  V : 𝒰 ℓv
  A : 𝒰 ℓ
  G : V → V → 𝒰 ℓe

vtx-surjective : is-surjective (vtx {G = G})
vtx-surjective = FG.elim-prop hlevel! λ v → ∣ v , refl ∣₁

universal : is-groupoid A
          → (FreeGpd G → A)
          ≃ Σ[ va ꞉ (V → A) ] ({x y : V} → G x y → va x ＝ va y)
universal {A} {V} {G} A-gpd = ≅→≃ $ iso inc back refl (fun-ext (fun-ext ∘ se')) where
  instance _ = hlevel-basic-instance 3 A-gpd
  inc : (FreeGpd G → A) → Σ[ va ꞉ (V → A) ] ({x y : V} → G x y → va x ＝ va y)
  inc f = f ∘ vtx , ap f ∘ edge
  back : Σ[ va ꞉ (V → A) ] ({x y : V} → G x y → va x ＝ va y) → FreeGpd G → A
  back = FG.rec A-gpd $ₜ²_
  se' : (f : FreeGpd G → A) (x : FreeGpd G) → back (inc f) x ＝ f x
  se' f =
    elim-set hlevel! (λ v → refl)
      λ e → to-pathᴾ (  transport-path refl _ _
                      ∙ ∙-pull-l (∙-id-i _)
                      ∙ ∙-inv-o _)

-- path properties

@0 connected-paths : ((x y : V) → vtx {G = G} x ＝ vtx y)
                   ≃ is-connected-graph G
connected-paths =
  Π-cod-≃ λ x →
  Π-cod-≃ λ y →
  FreeGpd-≃'

loop-free≃set : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
              → ((x : V) → (p : vtx {G = G} x ＝ vtx x) → p ＝ refl)
              ≃ is-set (FreeGpd G)
loop-free≃set =
  prop-extₑ!
    (λ lf → FG.elim-prop {C = λ p → ∀ q → is-prop (p ＝ q)} hlevel!
               λ vp → FG.elim-prop {C = λ q → is-prop (vtx vp ＝ q)} hlevel!
                 λ vq pq1 pq2 → ∙-cancel′-r (pq2 ⁻¹) pq1 pq2 (lf vp (pq1 ∙ pq2 ⁻¹) ∙ ∙-inv-i pq2 ⁻¹))
    λ sfg x p → sfg (vtx x) (vtx x) p refl

@0 circuit-free : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                → ((x : V) → (p : vtx {G = G} x ＝ vtx x) → p ＝ refl)
                ≃ is-circuit-free G
circuit-free =
  Π-cod-≃ λ x →
  Π-ap FreeGpd-≃' λ p →
    prop-extₑ!
      (λ e → ap (encode x) e ∙ encode-decode {fg = vtx x} nil)
      (λ e → decode-encode p ⁻¹ ∙ ap (decode (vtx x)) e)

@0 is-circuit-free≃set : {V : 𝒰 ℓ} {G : V → V → 𝒰 ℓe} -- why?
                       → is-circuit-free G ≃ is-set (FreeGpd G)
is-circuit-free≃set = circuit-free ⁻¹ ∙ loop-free≃set
