module UF.Base where

open import Prelude
open import Meta.Effect
open import Foundations.Sigma
open import Logic.Discreteness
open Variadics _

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Dec as Dec
open import Data.Maybe
open import Data.Maybe.Correspondences.Unary.Any
open import Data.List
open import Data.Acc
open import Data.Sum

open import KVListU
open import KVMapU

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

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

is-terminal : {g : Graph1 A} → is-UF-graph g → A → 𝒰
is-terminal {g} uf x = x ∈ uf .dom × (∀ {y} → ¬ Edge g x y)

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

is-nonterminal : Pnode A → 𝒰
is-nonterminal (nonterminal _) = ⊤
is-nonterminal (terminal _)  = ⊥

nonterminal≠terminal : {a b : A}
                     → nonterminal a ≠ terminal b
nonterminal≠terminal p = subst is-nonterminal p tt

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

record CGraph (A : 𝒰) : 𝒰 where
  constructor is-cgraph
  field
    mp     : PMap A
    ⦃ dv ⦄ : is-discrete A
    ac     : is-noeth (pmr mp)
    cl     : {x y : A} → pmr mp x y → y ∈ keysm mp

open CGraph public

to-spec : CGraph A → Graph1 A
to-spec c .grf x y =
  el (pmr (c .mp) x y)
     (any-is-of-hlevel 0 $ is-discrete→is-set Pnode-discrete (nonterminal y))
to-spec c .stv     = is-discrete→is-set (c .dv)
to-spec c .una p q = nonterminal-inj (∈ₘ-unique p q)

to-spec-uf : (c : CGraph A)
           → is-UF-graph (to-spec c)
to-spec-uf c .acy = c. ac
to-spec-uf c .dom = from-list (keysm (c .mp))
to-spec-uf c .coh = ⊆-list ∘ lookup→has {xs = c .mp .kv}
to-spec-uf c .clo = ⊆-list ∘ c .cl

tlink-fun : ⦃ d : is-discrete A ⦄ → A → A → PMap A → PMap A
tlink-fun a b = insertm a (nonterminal b) ∘ insertm b (terminal b)

tlink→edge : {a b : A} {c : CGraph A}
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
                         (λ x=b en → absurd (nonterminal≠terminal (unhere en)))
                         (λ x≠b → x≠b ,_)
                         (x ≟ b)) >)
     (x ≟ a)
   ∘ subst (λ q → nonterminal y ∈ₘ q)
           (kvlist-insert-lookup {xs = g'} x)

tlink←edge : {a b : A} {c : CGraph A}
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

tlink-keys≈ : {a b : A} {c : CGraph A} (a≠b : a ≠ b)
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

tlink : (a b : A) → a ≠ b
      → CGraph A
      → CGraph A
tlink a b a≠b c .mp = tlink-fun a b (c .mp)
tlink a b a≠b c .dv = c .dv
tlink a b a≠b c .ac =
  noeth-map
    (tlink→edge {c = c})
    (tlink-spec-uf a b a≠b (to-spec-uf c) .acy)
tlink a b a≠b c .cl =
    tlink-keys≈ {c = c} a≠b .snd
  ∘ tlink-spec-uf a b a≠b (to-spec-uf c) .clo
  ∘ tlink→edge {c = c} _ _
