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
open import Data.Sum as Sum

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

∉dom→terminal : {g : Graph1 A} → (iug : is-UF-graph g)
              → ∀ {x} → x ∉ iug .dom → is-terminal-node g x
∉dom→terminal iug x∉ = contra (iug .coh) x∉

empty-uf : (sa : is-set A) → is-UF-graph (empty1 sa)
empty-uf sa .acy x = acc λ y → false!
empty-uf sa .dom   = []
empty-uf sa .coh e = absurd e
empty-uf sa .clo e = absurd e

is-terminus : {g : Graph1 A} → is-UF-graph g → A → 𝒰
is-terminus {g} uf x = x ∈ uf .dom × is-terminal-node g x

is-terminus-sub : {g1 g2 : Graph1 A} {x : A}
                → (iug1 : is-UF-graph g1)
                → (iug2 : is-UF-graph g2)
                → (∀ {x y} → Edge g2 x y → Edge g1 x y)
                → iug1 .dom ⊆ iug2 .dom
                → is-terminus iug1 x
                → is-terminus iug2 x
is-terminus-sub {g1} {g2} iug1 iug2 f s (x∈ , t1) =
  (s x∈) , is-terminal-node-sub {g1 = g1} {g2 = g2} f t1 

-- set a -> b
linknt-grf : A → A
           → (A → A → 𝒰)
           → A → A → 𝒰

linknt-grf a b g x y = ((x ＝ a) × (y ＝ b)) ⊎ ((x ≠ a) × g x y)

linknt-grf-prop : is-set A
               → {g : A → A → 𝒰}
               → (∀ {x y} → is-prop (g x y))
               → {a b x y : A} → is-prop (linknt-grf a b g x y)
linknt-grf-prop sa sp =
  disjoint-⊎-is-prop hlevel!
    (×-is-of-hlevel 1 hlevel! sp)
    λ where ((x=a , _) , (x≠a , _)) → x≠a x=a
  where
    instance _ = hlevel-basic-instance 2 sa

linknt-spec : A → A
            → Graph1 A
            → Graph1 A
linknt-spec a b g .grf x y                                =
  el (linknt-grf a b (Edge g) x y)
     (linknt-grf-prop (g .stv) (prop-edge g {x = x} {y = y}))
linknt-spec a b g .stv                                    = g .stv
linknt-spec a b g .una (inl (x=a , y=b)) (inl (_ , z=b )) = y=b ∙ z=b ⁻¹
linknt-spec a b s .una (inl (x=a , _))   (inr (x≠a , _ )) = absurd (x≠a x=a)
linknt-spec a b s .una (inr (x≠a , _))   (inl (x=a , _ )) = absurd (x≠a x=a)
linknt-spec a b s .una (inr (_   , e))   (inr (_   , e')) = s .una e e'

-- linknt is a graph homomorphism when linking a terminal
linknt-spec-graph-hom : {a b : A} {c : Graph1 A}
                     → is-terminal-node c a
                     → ∀ {x y} → Edge c x y → Edge (linknt-spec a b c) x y
linknt-spec-graph-hom {c} ta {x} {y} e =
     inr ( contra (λ x=a → subst (λ q → Edge c q y) x=a e) ta
   , e)

linknt-spec-uf : (a b : A) → a ≠ b
              → {g : Graph1 A}
              → (iug : is-UF-graph g)
              → is-terminus iug b
              → is-UF-graph (linknt-spec a b g)
linknt-spec-uf a b a≠b {g} iug tb .acy =
  to-ninduction (iug .acy) _
    λ x ih → acc λ y →
       [ (λ where
               (_ , y=b) → acc λ z →
                  [ (λ where
                        (y=a , _) → absurd (a≠b (y=a ⁻¹ ∙ y=b)))
                  , (λ where
                        (_ , e) → absurd (tb .snd (subst (λ q → Edge g q z) y=b e)))
                  ]ᵤ)
       , (λ where
               (_ , e′) → ih y e′)
       ]ᵤ
linknt-spec-uf a b a≠b     iug tb .dom = a ∷ iug .dom
linknt-spec-uf a b a≠b     iug tb .coh (inl (x=a , _)) = hereₛ x=a
linknt-spec-uf a b a≠b     iug tb .coh (inr (_ , e))   = thereₛ (iug .coh e)
linknt-spec-uf a b a≠b     iug tb .clo {x} {y} =
  [ (λ where
        (_ , y=b) → thereₛ (subst (_∈ iug .dom) (y=b ⁻¹) (tb .fst)))
  , (λ where
        (_ , e′) → thereₛ (iug .clo e′))
  ]ᵤ

-- remove all edges from a
terminate-grf : A
              → (A → A → 𝒰)
              → A → A → 𝒰
terminate-grf a g x y = (x ≠ a) × g x y

terminate-grf-prop : {g : A → A → 𝒰}
                   → (∀ {x y} → is-prop (g x y))
                   → {a x y : A} → is-prop (terminate-grf a g x y)
terminate-grf-prop sp = ×-is-of-hlevel 1 hlevel! sp

terminate-spec : A
               → Graph1 A
               → Graph1 A
terminate-spec a g .grf x y               =
  el (terminate-grf a (Edge g) x y)
     (terminate-grf-prop (prop-edge g {x = x} {y = y}) {y = y})
terminate-spec a g .stv                   = g .stv
terminate-spec a g .una (_ , e1) (_ , e2) = g .una e1 e2

terminate-spec-graph-sub : {a : A} {c : Graph1 A}
                         → ∀ {x y} → Edge (terminate-spec a c) x y → Edge c x y 
terminate-spec-graph-sub (_ , e) = e

terminate-spec-graph-hom : {a : A} {c : Graph1 A}
                         → is-terminal-node c a
                         → ∀ {x y} → Edge c x y → Edge (terminate-spec a c) x y
terminate-spec-graph-hom {c} ta {x} {y} e = 
    contra (λ x=b → subst (λ q → Edge c q y) x=b e) ta
  , e

terminate-spec-uf : (a : A) 
                  → {g : Graph1 A}
                  → is-UF-graph g
                  → is-UF-graph (terminate-spec a g)
terminate-spec-uf a iug .acy = noeth-map (λ _ _ → snd) (iug .acy)
terminate-spec-uf a iug .dom = a ∷ iug .dom
terminate-spec-uf a iug .coh (_ , e) = thereₛ (iug .coh e)
terminate-spec-uf a iug .clo (_ , e) = thereₛ (iug .clo e)

terminate-spec-uf→terminus : {a : A} {g : Graph1 A}
                           → (iug : is-UF-graph g)
                           → is-terminus (terminate-spec-uf a iug) a
terminate-spec-uf→terminus iug = hereₛ refl , (λ where (a≠a , _) → a≠a refl)

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

-- linknt

linknt-fun : ⦃ d : is-discrete A ⦄ → A → A → PMap A → PMap A
linknt-fun a b = insertm a (nonterminal b)

linknt→edge : ⦃ d : is-discrete A ⦄
            → {a b : A} {c : CGraph A}
            → Π[ pmr (linknt-fun a b (c .mp)) ⇒ Edge (linknt-spec a b (to-spec c)) ]
linknt→edge {a} {b} {c} x y =
  Dec.elim
   {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                  then just (nonterminal b)
                                  else lookup-kv (c .mp .kv) x)
            → ((x ＝ a) × (y ＝ b)) ⊎ ((x ≠ a) × pmr (c .mp) x y)}
   (λ x=a → inl ∘ (x=a ,_) ∘ nonterminal-inj ∘ unhere)
   (λ x≠a → inr ∘ < (λ _ → x≠a) , id >)
   (x ≟ a)
   ∘ subst (λ q → nonterminal y ∈ₘ q)
           (kvlist-insert-lookup {xs = c .mp .kv} x)

linknt←edge : ⦃ d : is-discrete A ⦄
            → {a b : A} {c : CGraph A}
            → Π[ Edge (linknt-spec a b (to-spec c)) ⇒ pmr (linknt-fun a b (c .mp)) ]
linknt←edge {a} {b} {c} x y (inl (x=a , y=b))     =
  subst (nonterminal y ∈ₘ_)
        (kvlist-insert-lookup-= {xs = c .mp .kv} x=a ⁻¹) $
  here (ap nonterminal y=b)
linknt←edge {a} {b} {c} x y (inr (x≠a , e)) =
  subst (nonterminal y ∈ₘ_)
        (kvlist-insert-lookup-≠ {xs = c .mp .kv} x≠a ⁻¹) $
  e

linknt-keys : ⦃ d : is-discrete A ⦄
            → {a b : A} {c : CGraph A}
            → (tb : is-terminus (to-spec-uf c) b)
            → (a≠b : a ≠ b)
            → from-list (keysm (linknt-fun a b (c .mp))) ＝ linknt-spec-uf a b a≠b (to-spec-uf c) tb .dom
linknt-keys {a} {b} {c} tb a≠b =
  list-≈ (kvlist-upsert-≈ (c .mp .inv))

linknt : ⦃ d : is-discrete A ⦄
       → (a b : A)
       → a ≠ b
       → (c : CGraph A)
       → is-terminus (to-spec-uf c) b
       → CGraph A
linknt a b a≠b c tb .mp = linknt-fun a b (c .mp)
linknt a b a≠b c tb .ac =
  noeth-map
    (linknt→edge {c = c})
    (linknt-spec-uf a b a≠b (to-spec-uf c) tb .acy)
linknt a b a≠b c tb .cl {x} {y} =
    list-⊆
  ∘ subst (y ∈_) (linknt-keys {c = c} tb a≠b ⁻¹)
  ∘ linknt-spec-uf a b a≠b (to-spec-uf c) tb .clo
  ∘ linknt→edge {c = c} _ _

-- terminate

terminate-fun : ⦃ d : is-discrete A ⦄ → A → PMap A → PMap A
terminate-fun a = insertm a (terminal a)

terminate→edge : ⦃ d : is-discrete A ⦄
               → {a : A} {c : CGraph A}
               → Π[ pmr (terminate-fun a (c .mp)) ⇒ Edge (terminate-spec a (to-spec c)) ]
terminate→edge {a} {c} x y =
  subst (λ q → nonterminal y ∈ₘ q → (x ≠ a) × pmr (c .mp) x y)
        (kvlist-insert-lookup {xs = c .mp .kv} x ⁻¹) $
  Dec.elim
     {C = λ q → nonterminal y ∈ₘ (if ⌊ q ⌋
                                    then just (terminal a)
                                    else lookup-kv (c .mp .kv) x)
              → (x ≠ a) × pmr (c .mp) x y}
     (λ x=a en → absurd (terminal≠nonterminal (unhere en ⁻¹)))
     (λ x≠a → x≠a ,_)
     (x ≟ a)

terminate←edge : ⦃ d : is-discrete A ⦄
               → {a : A} {c : CGraph A}
               → Π[ Edge (terminate-spec a (to-spec c)) ⇒ pmr (terminate-fun a (c .mp)) ]
terminate←edge {a} {c} x y (x≠a , e) =
  subst (nonterminal y ∈ₘ_)
        (kvlist-insert-lookup-≠ {xs = c .mp .kv} x≠a ⁻¹)
        e

terminate-keys : ⦃ d : is-discrete A ⦄
                → {a : A} {c : CGraph A}
                → from-list (keysm (terminate-fun a (c .mp))) ＝ terminate-spec-uf a (to-spec-uf c) .dom
terminate-keys {a} {c} =
  list-≈ (kvlist-upsert-≈ (c .mp .inv))

terminate : ⦃ d : is-discrete A ⦄
          → (a : A)
          → CGraph A
          → CGraph A
terminate a c .mp = terminate-fun a (c .mp)
terminate a c .ac =
  noeth-map
    (terminate→edge {c = c})
    (terminate-spec-uf a (to-spec-uf c) .acy)
terminate a c .cl {x} {y} =
    list-⊆
  ∘ subst (y ∈_) (terminate-keys {c = c} ⁻¹)
  ∘ terminate-spec-uf a  (to-spec-uf c) .clo
  ∘ terminate→edge {c = c} _ _

is-terminus-terminate : ⦃ d : is-discrete A ⦄
                      → (a : A)
                      → (c : CGraph A)
                      → is-terminus (to-spec-uf (terminate a c)) a
is-terminus-terminate a c =
  is-terminus-sub
    (terminate-spec-uf a (to-spec-uf c))
    (to-spec-uf (terminate a c))
    (λ {x} {y} → terminate→edge {c = c} x y)
    (subst (_⊆ to-spec-uf (terminate a c) .dom) (terminate-keys {c = c}) id)
    (terminate-spec-uf→terminus (to-spec-uf c))

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

terminus-for : ⦃ d : is-discrete A ⦄
              → CGraph A → A → A → 𝒰
terminus-for c x y = is-terminus (to-spec-uf c) y
                    × (vtx {G = Edge (to-spec c)} y ＝ vtx x)

terminus-ty : ⦃ d : is-discrete A ⦄
            → CGraph A → A → 𝒰
terminus-ty {A} c x =
  Σ[ a ꞉ A ] terminus-for c x a


terminus-loop : ⦃ d : is-discrete A ⦄
                (c : CGraph A)
              → (x : A)
              → ((y : A) → pmr (c .mp) x y → y ∈ to-spec-uf c .dom → terminus-ty c y)
              → x ∈ to-spec-uf c .dom → terminus-ty c x
terminus-loop {A} c x ih x∈ =
  Maybe.rec-with-∈
    (lookupm (c .mp) x)
    (λ n → absurd (lookup→∉ (c .mp .inv) n (list-⊆ x∈)))
    λ where
         (nonterminal y) e →
            let (z , tz , ez) = ih y e (⊆-list (c .cl e))
              in
            z , tz , ez ∙ edge e ⁻¹
         (terminal y) e →
             x
           , pterm→terms {c = c} x
               (any-map (λ eq → subst is-terminal eq tt) e)
           , refl

terminus : ⦃ d : is-discrete A ⦄
         → (c : CGraph A)
         → (x : A) → terminus-ty c x ⊎ x ∉ to-spec-uf c .dom
terminus c x =
  Maybe.rec-with-∈
    (lookupm (c .mp) x)
    (inr ∘ ∉-list ∘ lookup→∉ (c .mp .inv))
    λ where
        (nonterminal v) a∈ →
           inl (to-ninduction (c .ac)
                  (λ z → z ∈ to-spec-uf c .dom → terminus-ty c z)
                  (terminus-loop c)
                  x (⊆-list (lookup→has {xs = c .mp .kv} a∈)))
        (terminal v)    a∈ →
           inl ( x
               , (  ⊆-list (lookup→has {xs = c .mp .kv} a∈)
                  , (λ {y} y∈ → terminal≠nonterminal (∈ₘ-unique a∈ y∈)))
               , refl)

terminus-or-out : ⦃ d : is-discrete A ⦄
                → CGraph A → A → A → 𝒰
terminus-or-out c x a = terminus-for c x a ⊎ ((a ＝ x) × (x ∉ to-spec-uf c .dom))

terminal-for : ⦃ d : is-discrete A ⦄
              → CGraph A → A → A → 𝒰
terminal-for c x y = is-terminal-node (to-spec c) y
                    × (vtx {G = Edge (to-spec c)} y ＝ vtx x)

terminus-or-out→terminal : ⦃ d : is-discrete A ⦄
                         → (c : CGraph A) → (x a : A)
                         → terminus-or-out c x a → terminal-for c x a
terminus-or-out→terminal c x a (inl ((_ , t) , e)) = t , e
terminus-or-out→terminal c x a (inr (a=x , x∉)) =
  ∉dom→terminal (to-spec-uf c) (subst (_∉ to-spec-uf c .dom) (a=x ⁻¹) x∉) , ap vtx a=x

terminus' : ⦃ d : is-discrete A ⦄
          → (c : CGraph A)
          → (x : A) → Σ[ a ꞉ A ] (terminus-or-out c x a)
terminus' c x = [ second inl , (λ n → x , inr (refl , n)) ]ᵤ (terminus c x)

linknt-term : ⦃ d : is-discrete A ⦄
            → {x : A}
            → (a b : A)
            → a ≠ b
            → (c : CGraph A)
            → terminus-or-out c x b
            → CGraph A
linknt-term a b ne cg (inl (tb , _)) = linknt a b ne cg tb 
linknt-term a b ne cg (inr _)        = linknt a b ne (terminate b cg) (is-terminus-terminate b cg)

linknt-term-graph-hom : ⦃ d : is-discrete A ⦄
                 → {z a b : A} {c : CGraph A}
                 → (ne : a ≠ b)
                 → is-terminal-node (to-spec c) a
                 → (st : terminus-or-out c z b)
                 → ∀ {x y} → Edge (to-spec c) x y → Edge (to-spec (linknt-term a b ne c st)) x y
linknt-term-graph-hom {z} {a} {b} {c} ne ta (inl (tb , e))   {x} {y} =
    linknt←edge {c = c} x y
  ∘ linknt-spec-graph-hom {c = to-spec c} ta
linknt-term-graph-hom {z} {a} {b} {c} ne ta (inr (b=z , z∉)) {x} {y} =
    linknt←edge {c = terminate b c} x y
  ∘ linknt-spec-graph-hom {c = to-spec (terminate b c)}
       (is-terminal-node-sub {g1 = to-spec c} {g2 = to-spec (terminate b c)}
         (λ {x = x'} {y = y'} →
                terminate-spec-graph-sub {c = to-spec c} {y = y'}
              ∘ terminate→edge {c = c} x' y') ta)
  ∘ terminate←edge {a = b} {c = c} x y
  ∘ terminate-spec-graph-hom {c = to-spec c}
       (∉dom→terminal (to-spec-uf c)
       (subst (_∉ from-list (keysm (c .mp))) (b=z ⁻¹) z∉))

-- API

equated : ⦃ d : is-discrete A ⦄
        → CGraph A → List A
equated c = keysm (c .mp)

unequal : ⦃ d : is-discrete A ⦄
        → CGraph A
unequal .mp = emptym
unequal .ac x = acc λ y → false!
unequal .cl = false!

canonize : ⦃ d : is-discrete A ⦄
         → CGraph A → A → A
canonize cg = fst ∘ terminus' cg

equivalent : ⦃ d : is-discrete A ⦄
           → CGraph A → A → A → Bool
equivalent cg a b = canonize cg a =? canonize cg b

-- aka union
equate : ⦃ d : is-discrete A ⦄
       → A → A → CGraph A → CGraph A
equate a b cg =
  let a' = canonize cg a
      (b' , st) = terminus' cg b
    in
  Dec.rec
     (λ _ → cg)
     (λ ne → linknt-term a' b' ne cg st)
     (a' ≟ b')

-- properties

equated-dom : ⦃ d : is-discrete A ⦄
            → {c : CGraph A}
            → equated c ≈ to-spec-uf c .dom
equated-dom = ⊆-list , list-⊆

canonize-term : ⦃ d : is-discrete A ⦄
              → {c : CGraph A} {x : A}
              → terminal-for c x (canonize c x)
canonize-term {c} {x} =
  terminus-or-out→terminal c x (canonize c x) (snd $ terminus' c x)

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
  let (a' , ta) = terminus' c a
      (b' , tb) = terminus' c b
    in
  Dec.elim
     {C = λ q → Edge (to-spec (Dec.rec (λ _ → c) (λ ne → linknt-term a' b' ne c tb) q)) x y}
     (λ _ → e)
     (λ a'≠b' → linknt-term-graph-hom {c = c} a'≠b' (terminus-or-out→terminal c a a' ta .fst) tb e)
     (a' ≟ b')

@0 equate-equivalent : ⦃ d : is-discrete A ⦄
                     → {c : CGraph A} {x : A} {y : A}
                     → vtx {G = Edge (to-spec (equate x y c))} x ＝ vtx y
equate-equivalent {c} {x} {y} =
  let (x' , tx) = terminus' c x
      (tx' , ex) = terminus-or-out→terminal c x x' tx
      (y' , ty) = terminus' c y
      (ty' , ey) = terminus-or-out→terminal c y y' ty
      equate-lift = FG.map-hom {G = Edge (to-spec c)} id (equate-graph-hom {a = x} {b = y} {c = c})
    in
    ap equate-lift ex ⁻¹
  ∙ so→true! ⦃ equivalent-reflects {c = equate x y c} ⦄
      (Dec.elim
       {C = λ q → ⌞ equivalent (Dec.rec (λ _ → c) (λ ne → linknt-term x' y' ne c ty) q) x' y' ⌟}
       (λ cx=cy → true→so! ⦃ equivalent-reflects {c = c} ⦄
                    (ap vtx cx=cy))
       (λ cx≠cy → true→so! ⦃ equivalent-reflects {c = linknt-term x' y' cx≠cy c ty} ⦄
                    (edge (Sum.elim
                            {C = λ q → Edge (to-spec (linknt-term x' y' cx≠cy c q)) x' y'}
                            (λ a → linknt←edge {c = c} x' y' (inl (refl , refl)))
                            (λ b → linknt←edge {c = terminate y' c} x' y' (inl (refl , refl)))
                            ty)))
       (x' ≟ y'))
  ∙ ap equate-lift ey
