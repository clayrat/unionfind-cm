module UF.Base where

open import Prelude
open import Meta.Effect
open import Foundations.Sigma
open import Logic.Discreteness
open Variadics _

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.All
open import Data.Maybe.Correspondences.Unary.Any
open import Data.List
open import Data.List.Correspondences.Unary.Unique
open import Data.Acc
open import Data.Sum

open import KVListU
open import KVMapU

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import RPath as RP
open import FreeGpd as FG
open import Graph1

private variable
  A V : 𝒰

open KVListU.Ops
open KVOps
open KVOps2

-- acyclic + finitary + closed
record is-UF-graph (g : Graph1 A) : 𝒰₁ where
  constructor mk-iug
  field
    acy : is-acyclic g
    dom : LFSet A
    coh : {x y : A} → Edge g x y → x ∈ dom
    clo : {x y : A} → Edge g x y → y ∈ dom

open is-UF-graph public

empty-uf : (sa : is-set A) → is-UF-graph (empty1 sa)
empty-uf sa .acy x = acc λ y → false!
empty-uf sa .dom   = []
empty-uf sa .coh e = absurd e
empty-uf sa .clo e = absurd e

is-terminus : {g : Graph1 A} → is-UF-graph g → A → 𝒰
is-terminus {g} uf x = x ∈ uf .dom × is-terminal-node g x

-- set a -> b (assuming they are not equal and terminal)
tlink-grf : A → A
          → (A → A → 𝒰)
          → A → A → 𝒰
tlink-grf a b g x y = ((x ＝ a) × (y ＝ b)) ⊎ ((x ≠ a) × (x ≠ b) × g x y)

tlink-grf-prop : is-set A
               → {g : A → A → 𝒰}
               → (∀ {x y} → is-prop (g x y))
               → {a b x y : A} → is-prop (tlink-grf a b g x y)
tlink-grf-prop sa sp =
  disjoint-⊎-is-prop hlevel!
    (×-is-of-hlevel 1 hlevel! (×-is-of-hlevel 1 hlevel! sp))
    λ where ((x=a , _) , (x≠a , _)) → x≠a x=a
  where
    instance _ = hlevel-basic-instance 2 sa

tlink-spec : A → A
           → Graph1 A
           → Graph1 A
tlink-spec a b g .grf x y                                     =
  el (tlink-grf a b (Edge g) x y)
     (tlink-grf-prop (g .stv) (prop-edge g {x = x} {y = y}))
tlink-spec a b g .stv                                         = g .stv
tlink-spec a b g .una (inl (x=a , y=b))   (inl (_ , z=b))     = y=b ∙ z=b ⁻¹
tlink-spec a b s .una (inl (x=a , _))     (inr (x≠a , _ , _)) = absurd (x≠a x=a)
tlink-spec a b s .una (inr (x≠a , _ , _)) (inl (x=a , _))     = absurd (x≠a x=a)
tlink-spec a b s .una (inr (_ , _ , e))   (inr (_ , _ , e'))  = s .una e e'

-- tlink is a graph homomorphism when linking terminals
tlink-spec-graph-hom : {a b : A} {c : Graph1 A}
                     → is-terminal-node c a
                     → is-terminal-node c b
                     → ∀ {x y} → Edge c x y → Edge (tlink-spec a b c) x y
tlink-spec-graph-hom {c} ta tb {x} {y} e =
     inr ( contra (λ x=a → subst (λ q → Edge c q y) x=a e) ta
   , contra (λ x=b → subst (λ q → Edge c q y) x=b e) tb
   , e)

tlink-spec-uf : (a b : A) → a ≠ b
              → {g : Graph1 A}
              → is-UF-graph g
              → is-UF-graph (tlink-spec a b g)
tlink-spec-uf a b a≠b iug .acy =
  to-ninduction (iug .acy) _
    λ x ih → acc λ y →
       [ (λ where
               (_ , y=b) → acc λ z →
                  [ (λ where
                        (y=a , _) → absurd (a≠b (y=a ⁻¹ ∙ y=b)))
                  , (λ where
                        (_ , y≠b , _) → absurd (y≠b y=b))
                  ]ᵤ)
       , (λ where
               (_ , _ , e′) → ih y e′)
       ]ᵤ
tlink-spec-uf a b a≠b iug .dom = a ∷ b ∷ iug .dom
tlink-spec-uf a b a≠b iug .coh (inl (x=a , _))   = hereₛ x=a
tlink-spec-uf a b a≠b iug .coh (inr (_ , _ , e)) = thereₛ (thereₛ (iug .coh e))
tlink-spec-uf a b a≠b iug .clo {x} {y} =
  [ (λ where
        (_ , y=b) → thereₛ (hereₛ y=b))
  , (λ where
        (_ , _ , e′) → thereₛ (thereₛ (iug .clo e′)))
  ]ᵤ

-- partition nodes

data Pnode (A : 𝒰) : 𝒰 where
  nonterminal : A → Pnode A
  terminal    : A → Pnode A

nodeval : Pnode A → A
nodeval (nonterminal a) = a
nodeval (terminal a)    = a

is-nonterminal? : Pnode A → Bool
is-nonterminal? (nonterminal _) = true
is-nonterminal? (terminal _)    = false

is-terminal? : Pnode A → Bool
is-terminal? = not ∘ is-nonterminal?

is-terminal : Pnode A → 𝒰
is-terminal (nonterminal _) = ⊥
is-terminal (terminal _)  = ⊤

instance
  Reflects-is-terminal : {x : Pnode A} → Reflects (is-terminal x) (is-terminal? x)
  Reflects-is-terminal {x = nonterminal x} = ofⁿ id
  Reflects-is-terminal {x = terminal x}    = ofʸ tt

  Dec-is-terminal : {x : Pnode A} → Dec (is-terminal x)
  Dec-is-terminal {x} .does = is-terminal? x
  Dec-is-terminal     .proof = Reflects-is-terminal

terminal≠nonterminal : {a b : A}
                     → terminal a ≠ nonterminal b
terminal≠nonterminal p = subst is-terminal p tt

nonterminal-inj : {a b : A}
                → nonterminal a ＝ nonterminal b
                → a ＝ b
nonterminal-inj = ap nodeval

terminal-inj : {a b : A}
             → terminal a ＝ terminal b
             → a ＝ b
terminal-inj = ap nodeval

unwrap : Pnode A → A × Bool
unwrap = < nodeval , is-nonterminal? >

wrap : A × Bool → Pnode A
wrap (a , b) = if b then nonterminal a else terminal a

Pnode-≃ : Pnode A ≃ A × Bool
Pnode-≃ =
  ≅→≃ $
  make-iso unwrap wrap $
  make-inverses
    (fun-ext (λ where
                  (a , false) → refl
                  (a , true) → refl))
    (fun-ext λ where
                 (nonterminal x) → refl
                 (terminal x) → refl)

instance
  Pnode-discrete : ⦃ d : is-discrete A ⦄
                 → is-discrete (Pnode A)
  Pnode-discrete = ↣→is-discrete (↪→↣ $ ≃→↪ Pnode-≃) auto

-- partition graph (computational)

PMap : 𝒰 → 𝒰
PMap A = KVMap A (Pnode A)

pmr : ⦃ d : is-discrete A ⦄ → PMap A → A → A → 𝒰
pmr p x y = nonterminal y ∈ₘ lookupm p x

oterm : ⦃ d : is-discrete A ⦄ → PMap A → A → 𝒰
oterm p x = All is-terminal (lookupm p x)

pterm : ⦃ d : is-discrete A ⦄ → PMap A → A → 𝒰
pterm p x = Any is-terminal (lookupm p x)

record CGraph (A : 𝒰) ⦃ d : is-discrete A ⦄ : 𝒰 where
  constructor is-cgraph
  field
    mp : PMap A
    ac : is-noeth (pmr mp)
    cl : {x y : A} → pmr mp x y → y ∈ keysm mp

open CGraph public

-- TODO reuse subtype infra?

mp-injective : ⦃ d : is-discrete A ⦄ → Injective (mp {A = A})
mp-injective {A} {x = is-cgraph mpx acx clx} {y = is-cgraph mpy acy cly} e =
 ap² {B = λ mp → is-noeth (pmr mp)
               × ({x y : A} → pmr mp x y
                            → y ∈ keysm mp)}
   (λ x (ea , ac) → is-cgraph x ea ac)
   e
   (to-pathᴾ (×-path ((Π-is-of-hlevel 1 λ x → hlevel 1) _ acy)
                     ((∀-is-of-hlevel 1 λ x → ∀-is-of-hlevel 1 λ y → fun-is-of-hlevel 1 $
                       Uniq-set→is-unique (is-discrete→is-set auto) (mpy .inv) y) _ _)))

instance
  CGraph-discrete : ⦃ d : is-discrete A ⦄
                  → is-discrete (CGraph A)
  CGraph-discrete ⦃ d ⦄ = ↣→is-discrete (mp , mp-injective) auto

to-spec : ⦃ d : is-discrete A ⦄ → CGraph A → Graph1 A
to-spec c .grf x y =
  el (pmr (c .mp) x y)
     (any-is-of-hlevel 0 $ is-discrete→is-set Pnode-discrete (nonterminal y))
to-spec c .stv     = is-discrete→is-set auto
to-spec c .una p q = nonterminal-inj (∈ₘ-unique p q)

to-spec-uf : ⦃ d : is-discrete A ⦄
           → (c : CGraph A)
           → is-UF-graph (to-spec c)
to-spec-uf c .acy = c. ac
to-spec-uf c .dom = from-list (keysm (c .mp))
to-spec-uf c .coh = ⊆-list ∘ lookup→has {xs = c .mp .kv}
to-spec-uf c .clo = ⊆-list ∘ c .cl

tlink-fun : ⦃ d : is-discrete A ⦄ → A → A → PMap A → PMap A
tlink-fun a b = insertm a (nonterminal b) ∘ insertm b (terminal b)

tlink→edge : ⦃ d : is-discrete A ⦄
           → {a b : A} {c : CGraph A}
           → Π[ pmr (tlink-fun a b (c .mp)) ⇒ Edge (tlink-spec a b (to-spec c)) ]
tlink→edge {a} {b} {c} x y =
  let g' = insert-kv b (terminal b) (c .mp .kv)
    in
    Dec.elim
     {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                    then just (nonterminal b)
                                    else lookup-kv g' x)
              → ((x ＝ a) × (y ＝ b)) ⊎ ((x ≠ a) × (x ≠ b) × pmr (c .mp) x y)}
     (λ x=a → inl ∘ (x=a ,_)
            ∘ nonterminal-inj ∘ unhere)
     (λ x≠a → inr
            ∘ < (λ _ → x≠a)
              , subst (λ q → nonterminal y ∈ₘ q → (x ≠ b) × pmr (c .mp) x y)
                      (kvlist-insert-lookup {xs = c .mp .kv} x ⁻¹)
                      (Dec.elim
                         {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                                        then just (terminal b)
                                                        else lookup-kv (c .mp .kv) x)
                                  → (x ≠ b) × pmr (c .mp) x y}
                         (λ x=b en → absurd (terminal≠nonterminal (unhere en ⁻¹)))
                         (λ x≠b → x≠b ,_)
                         (x ≟ b)) >)
     (x ≟ a)
   ∘ subst (λ q → nonterminal y ∈ₘ q)
           (kvlist-insert-lookup {xs = g'} x)

tlink←edge : ⦃ d : is-discrete A ⦄
           → {a b : A} {c : CGraph A}
           → Π[ Edge (tlink-spec a b (to-spec c)) ⇒ pmr (tlink-fun a b (c .mp)) ]
tlink←edge {a} {b} {c} x y (inl (x=a , y=b))     =
  subst (nonterminal y ∈ₘ_)
        (kvlist-insert-lookup-= {xs = insert-kv b (terminal b) (c .mp .kv)} x=a ⁻¹) $
  here (ap nonterminal y=b)
tlink←edge {a} {b} {c} x y (inr (x≠a , x≠b , e)) =
  subst (nonterminal y ∈ₘ_)
        (kvlist-insert-lookup-≠ {xs = insert-kv b (terminal b) (c .mp .kv)} x≠a ⁻¹) $
  subst (nonterminal y ∈ₘ_)
        (kvlist-insert-lookup-≠ {xs = c .mp .kv} x≠b ⁻¹) $
  e

-- TODO tlink≃edge ?

tlink-keys≈ : ⦃ d : is-discrete A ⦄
           → {a b : A} {c : CGraph A}
           → (a≠b : a ≠ b)
           → keysm (tlink-fun a b (c .mp)) ≈ tlink-spec-uf a b a≠b (to-spec-uf c) .dom
tlink-keys≈ {a} {b} {c} a≠b =
  Comp-≈ ⦃ m₂ = Membership-List ⦄ ._∙_
         {x = keysm (tlink-fun a b (c .mp))}
         {z = tlink-spec-uf a b a≠b (to-spec-uf c) .dom}
    (kvlist-upsert-≈ (Is-kvlist-upsert (c .mp .inv)))
    (Comp-≈ ⦃ m₁ = Membership-List ⦄ ⦃ m₂ = Membership-List ⦄ ._∙_
            {z = tlink-spec-uf a b a≠b (to-spec-uf c) .dom}
       (≈-∷ (kvlist-upsert-≈ (c .mp .inv)))
       (⊆-list , list-⊆))

tlink : ⦃ d : is-discrete A ⦄
      → (a b : A) → a ≠ b
      → CGraph A
      → CGraph A
tlink a b a≠b c .mp = tlink-fun a b (c .mp)
tlink a b a≠b c .ac =
  noeth-map
    (tlink→edge {c = c})
    (tlink-spec-uf a b a≠b (to-spec-uf c) .acy)
tlink a b a≠b c .cl =
    tlink-keys≈ {c = c} a≠b .snd
  ∘ tlink-spec-uf a b a≠b (to-spec-uf c) .clo
  ∘ tlink→edge {c = c} _ _

oterm→term : ⦃ d : is-discrete A ⦄
           → {c : CGraph A}
           → Π[ oterm (c .mp) ⇒ is-terminal-node (to-spec c) ]
oterm→term {c} x otm {y} =
  Maybe.All→∀∈ otm (nonterminal y)

term→oterm : ⦃ d : is-discrete A ⦄
           → {c : CGraph A}
           → Π[ is-terminal-node (to-spec c) ⇒ oterm (c .mp) ]
term→oterm {c} x with lookup-kv (c .mp .kv) x
... | just (nonterminal y) = λ c → absurd (c (here refl))
... | just (terminal y) = λ _ → just tt
... | nothing = λ _ → nothing

pterm→terms : ⦃ d : is-discrete A ⦄
           → {c : CGraph A}
           → Π[ pterm (c .mp) ⇒ is-terminus (to-spec-uf c) ]
pterm→terms {c} x ptm =
  let  (y , y∈ , yt) = Maybe.Any→Σ∈ ptm in
    ⊆-list (lookup→has {xs = c .mp .kv} y∈)
  , λ {y} ey → subst is-terminal (∈ₘ-unique y∈ ey) yt

terms→pterm : ⦃ d : is-discrete A ⦄
           → {c : CGraph A}
           → Π[ is-terminus (to-spec-uf c) ⇒ pterm (c .mp) ]
terms→pterm {c} x (x∈ , ne) with lookup←has (c .mp .inv) (list-⊆ {xs = keysm (c .mp)} x∈)
... | nonterminal y , _ , y∈l = absurd (ne y∈l)
... | terminal    y , _ , y∈l = Maybe.∈→Any y∈l tt

-- TODO pterm≃term

terminus-ty : ⦃ d : is-discrete A ⦄
            → CGraph A → A → 𝒰
terminus-ty {A} c x =
  Σ[ a ꞉ A ] is-terminus (to-spec-uf c) a
           × (vtx {G = Edge (to-spec c)} a ＝ vtx x)

oterminus-for : ⦃ d : is-discrete A ⦄
              → CGraph A → A → A → 𝒰
oterminus-for c x y = is-terminal-node (to-spec c) y
                    × (vtx {G = Edge (to-spec c)} y ＝ vtx x)

oterminus-ty : ⦃ d : is-discrete A ⦄
            → CGraph A → A → 𝒰
oterminus-ty {A} c x =
  Σ[ a ꞉ A ] oterminus-for c x a

terminus→oterminus : ⦃ d : is-discrete A ⦄
                     {c : CGraph A}
                   → Π[ terminus-ty c ⇒ oterminus-ty c ]
terminus→oterminus x (a , ta , ea) = a , ta .snd , ea

terminus-loop : ⦃ d : is-discrete A ⦄
                (c : CGraph A)
              → (x : A)
              → ((y : A) → pmr (c .mp) x y → y ∈ to-spec-uf c .dom → terminus-ty c y)
              → x ∈ to-spec-uf c .dom → terminus-ty c x
terminus-loop {A} c x ih x∈ =
  Maybe.elim
    (λ m → lookupm (c .mp) x ＝ m → terminus-ty c x)
    (λ n → absurd (lookup→∉ (c .mp .inv) n (list-⊆ x∈)))
    (λ where
         (nonterminal y) e →
            let ye = =just→∈ e
                (z , tz , ez) = ih y ye (⊆-list (c .cl ye))
              in
            z , tz , ez ∙ edge ye ⁻¹
         (terminal y) e →
             x
           , pterm→terms {c = c} x
               (subst (λ q → Any is-terminal q) (e ⁻¹) (here tt))
           , refl)
    (lookupm (c .mp) x) refl

terminus : ⦃ d : is-discrete A ⦄
         → (c : CGraph A)
         → (x : A) → oterminus-ty c x
terminus c x =
  Maybe.elim
    (λ m → lookupm (c .mp) x ＝ m → oterminus-ty c x)
    (λ n → x , (λ {y} e → false! (subst (nonterminal y ∈_) n e)) , refl)
    (λ where
         (nonterminal z) eq →
             terminus→oterminus {c = c} x $
             to-ninduction (c .ac)
               (λ z → z ∈ to-spec-uf c .dom → terminus-ty c z)
               (terminus-loop c)
               x (⊆-list (lookup→has {xs = c .mp .kv} (=just→∈ eq)))
         (terminal z) eq →
            x , (λ {y} e → terminal≠nonterminal (unhere (subst (nonterminal y ∈_) eq e) ⁻¹)) , refl)
    (lookupm (c .mp) x) refl

-- API

equated : ⦃ d : is-discrete A ⦄
        → CGraph A → List A
equated c = keysm (c .mp)

unequal : ⦃ d : is-discrete A ⦄
        → CGraph A
unequal .mp = emptym
unequal .ac x = acc λ y → false!
unequal .cl = false!

-- aka find
canonize : ⦃ d : is-discrete A ⦄
         → CGraph A → A → A
canonize cg = fst ∘ terminus cg

equivalent : ⦃ d : is-discrete A ⦄
           → CGraph A → A → A → Bool
equivalent cg a b = canonize cg a =? canonize cg b

-- aka union
equate : ⦃ d : is-discrete A ⦄
       → A → A → CGraph A → CGraph A
equate a b cg =
  let (a' , ta , ea) = terminus cg a
      (b' , tb , eb) = terminus cg b
    in
  Dec.rec
    (λ _ → cg)
    (λ ne → tlink a' b' ne cg)
    (a' ≟ b')

-- properties

equated-dom : ⦃ d : is-discrete A ⦄
            → {c : CGraph A}
            → equated c ≈ to-spec-uf c .dom
equated-dom = ⊆-list , list-⊆

-- unequal-empty : ⦃ d : is-discrete A ⦄

canonize-term : ⦃ d : is-discrete A ⦄
              → {c : CGraph A} {x : A}
              → oterminus-for c x (canonize c x)
canonize-term {c} {x} = snd $ terminus c x

@0 equivalent-reflects : ⦃ d : is-discrete A ⦄
                       → {c : CGraph A} {x : A} {y : A}
                       → Reflects (vtx {G = Edge (to-spec c)} x ＝ vtx y) (equivalent c x y)
equivalent-reflects ⦃ d ⦄ {c} {x} {y} =
  let (tx , ex) = canonize-term {c = c} {x = x}
      (ty , ey) = canonize-term {c = c} {x = y}
    in
  Reflects.dmap
    (λ ec → ex ⁻¹ ∙ ap vtx ec ∙ ey)
    (contra λ e →
       graph1-terminal {g = to-spec c} tx ty $
       FreeGpd-≃ $
       ex ∙ e ∙ ey ⁻¹)
    (Reflects-does ⦃ P? = d ⦄)

equate-graph-hom : ⦃ d : is-discrete A ⦄
                 → {a b : A} {c : CGraph A}
                 → ∀ {x y} → Edge (to-spec c) x y → Edge (to-spec (equate a b c)) x y
equate-graph-hom {a} {b} {c} {x} {y} e =
  let (a' , ta , ea) = terminus c a
      (b' , tb , eb) = terminus c b
    in
  Dec.elim
     {C = λ q → Edge (to-spec (Dec.rec (λ _ → c) (λ ne → tlink a' b' ne c) q)) x y}
     (λ a'=b' → e)
     (λ a'≠b' → tlink←edge {c = c} x y (tlink-spec-graph-hom {c = to-spec c} ta tb e))
     (a' ≟ b')

@0 equate-equivalent : ⦃ d : is-discrete A ⦄
                     → {c : CGraph A} {x : A} {y : A}
                     → vtx {G = Edge (to-spec (equate x y c))} x ＝ vtx y
equate-equivalent {c} {x} {y} =
  let (x' , tx , ex) = terminus c x
      (y' , ty , ey) = terminus c y
      equate-lift = FG.map-hom id (equate-graph-hom {a = x} {b = y} {c = c})
    in
    ap equate-lift ex ⁻¹
  ∙ so→true! ⦃ equivalent-reflects {c = equate x y c} ⦄
      (Dec.elim
       {C = λ q → ⌞ equivalent (Dec.rec (λ _ → c) (λ ne → tlink x' y' ne c) q) x' y' ⌟}
       (λ cx=cy → true→so! ⦃ equivalent-reflects {c = c} ⦄
                    (ap vtx cx=cy))
       (λ cx≠cy → true→so! ⦃ equivalent-reflects {c = tlink x' y' cx≠cy c} ⦄
                    (edge (tlink←edge {c = c} x' y' (inl (refl , refl)))))
       (x' ≟ y'))
  ∙ ap equate-lift ey
