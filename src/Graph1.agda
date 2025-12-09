module Graph1 where

open import Prelude
open import Meta.Effect
open import Foundations.Sigma
open Variadics _

open import Data.Empty hiding (_≠_)
open import Data.Acc
open import Data.Flip
open import Data.Star

open import RPath as RP
open import FreeGpd as FG

private variable
  A V : 𝒰

-- unary graph

record Graph1 (V : 𝒰) : 𝒰₁ where
  constructor is-graph1
  field
    grf : V → V → Prop 0ℓ                                   --  not a multigraph
    stv : is-set V
    una : {x y z : V} → ⌞ grf x y ⌟ → ⌞ grf x z ⌟ → y ＝ z  -- no more than one sink per node

open Graph1 public

Edge : Graph1 A → A → A → 𝒰
Edge g x y = ⌞ g .grf x y ⌟

prop-edge : {g : Graph1 A} → ∀ {x y} → is-prop (Edge g x y)
prop-edge {g} {x} {y} = g .grf x y .n-Type.carrier-is-tr

Path1 : Graph1 A → A → A → 𝒰
Path1 = Star ∘ Edge

RPath1 : Graph1 A → A → A → 𝒰
RPath1 = RPath ∘ Edge

is-acyclic : Graph1 A → 𝒰
is-acyclic = is-noeth ∘ Edge

prop-paths : Graph1 A → 𝒰
prop-paths g = ∀ x y → is-prop (Path1 g x y)

-- reduced path which looks like this after normalization: x ----> z <---- y
is-cospan : {g : Graph1 A} {x y : A}
          → RPath1 g x y
          → 𝒰
is-cospan {A} {g} {x} {y} r =
  Σ[ z ꞉ A ] Σ[ f ꞉ Path1 g x z ] Σ[ b ꞉ Path1 g y z ] (r ＝ RP.concat (embed f) (mirror b))

-- in a unary graph, every reduced path is a cospan
-- (prop-truncated to avoid fiddling with equations)
graph1→cospan : {g : Graph1 A} {x y : A}
              → (r : RPath1 g x y)
              → ∥ is-cospan {g = g} r ∥₁
graph1→cospan {A} {g} = RP.elim-prop go
  where
  go : RP.Elim-prop λ {x} {y} q → ∥ is-cospan {g = g} q ∥₁
  go .εʳ {x} {y} e =
    ∣ y , ε e , refl , concat-nil-r ⁻¹ ∣₁
  go .◅~ʳ             (fwd exy)       ih =
    -- cons the forward edge
    map
      (λ where
           (w , f , b , e) → w , exy ◅ f , b , ap (fwd exy ◅~_) e)
      ih
  go .◅~ʳ {x} {y} {z} (bwd eyx) {gyz} ih =
    map
      (λ where
           -- if the forward part is empty, snoc the backward edge
           (w , ε y=w     , b , e) →
              Jₚ (λ t et → (etx : Edge g t x) → (gtz : RPath1 g t z)
                         → gtz ＝ RP.concat (embed (ε (et ⁻¹))) (mirror b)
                         → is-cospan {g = g} (bwd etx ◅~ gtz))
                 (λ etx gtz e' →
                      x , refl , b ◅+ etx
                    ,   ap (bwd etx ◅~_) (e' ∙ concat-nil-l)
                      ∙ mirror-snoc b etx ⁻¹
                      ∙ concat-nil-l ⁻¹)
                 (y=w ⁻¹) eyx gyz e
           -- otherwise, we must have a trivial loop, cancel it out
           (w , eyv ◅ fvw , b , e) →
              Jₚ (λ q eq → (eyv : Edge g y q) → (fvw : Path1 g q w)
                         → gyz ＝ RP.concat (embed (eyv ◅ fvw)) (mirror b)
                         → is-cospan {g = g} (bwd eyx ◅~ gyz))
                 (λ eyv' fvw' e' →
                          w , fvw' , b
                        ,   ap (bwd eyx ◅~_) e'
                          ∙ ap (λ j → (bwd eyx ◅~ (fwd j ◅~ RP.concat (embed fvw') (mirror b))))
                               (prop-edge {g = g} eyv' eyx)
                          ∙ bwdfwd)
                 (g .una eyx eyv) eyv fvw e)
      ih
  go .truncʳ r = hlevel!

acy1→prop-paths : {g : Graph1 A}
                → is-acyclic g
                → prop-paths g
acy1→prop-paths {g} acy =
  to-ninduction acy _
    λ x ih y →
      λ where
          (ε eqp)  (ε eqq)  → ap ε (path-is-of-hlevel 1 (g .stv) _ _ eqp eqq)
          (ε eqp)  (eq ◅ q) → absurd (noeth→acyclic acy y _ x q eq (ε (eqp ⁻¹)))
          (ep ◅ p) (ε eqq)  → absurd (noeth→acyclic acy y _ x p ep (ε (eqq ⁻¹)))
          (ep ◅ p) (eq ◅ q) →
             Jₚ (λ w ew → (ep′ : Edge g x _) → (eq′ : Edge g x w)
                        → (p′ : Path1 g _ y) → (q′ : Path1 g w y)
                        → (ep′ ◅ p′) ＝ (eq′ ◅ q′))
                (λ ep′ eq′ p′ q′ → ap² _◅_ (prop-edge {g = g} ep′ eq′)
                                           (ih _ ep′ y p′ q′))
                (g .una ep eq) ep eq p q

acy1→circuit-free : {g : Graph1 A}
                  → is-acyclic g
                  → is-circuit-free (Edge g)
acy1→circuit-free {g} acy x r =
  rec!
    (λ w fs bs e →
        e
      ∙ ap (λ q → RP.concat (embed fs) (mirror q))
           (acy1→prop-paths {g = g} acy x w fs bs ⁻¹)
      ∙ concat-embed-mirror fs)
    (graph1→cospan {g = g} r)

@0 acy1→freegpd-set : {g : Graph1 A}
                    → is-acyclic g
                    → is-set (FreeGpd (Edge g))
acy1→freegpd-set {g} acy = is-circuit-free≃set $ acy1→circuit-free {g = g} acy
