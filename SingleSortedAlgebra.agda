{- Singed-sorted algebras as  containers
   Based on the Multi-sorted version by Andreas Abel
-}

-- Preliminaries
-- =============

-- We import library content for indexed containers, standard types, and setoids.

open import Level

open import Data.Container                         using (Container; ⟦_⟧; μ; _▷_)
open import Data.Container.FreeMonad               using (_⋆C_)
open import Data.W                                 using (sup)

open import Data.Product                           using (Σ; _×_; _,_; Σ-syntax); open Σ
open import Data.Sum                               using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty.Polymorphic                 using (⊥; ⊥-elim)

open import Function                               using (_∘_)
open import Function.Bundles                       using (Func)

open import Relation.Binary                        using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality  using (_≡_; refl)
open import Relation.Unary                         using (Pred)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Setoid using (Carrier; _≈_; isEquivalence)
open Func renaming (f to apply)

-- Letter ℓ denotes universe levels.

variable
  ℓ ℓ' ℓᵒ ℓᵃ ℓᵐ ℓᵉ ℓⁱ : Level
  I : Set ℓⁱ

-- The interpretation of a container (Op ◃ Ar) is
--
--   ⟦ Op ◃ Ar ⟧ X = Σ[ o ∈ Op ] ((i : Ar o) → X)
--
-- which contains pairs consisting of an operator $o$ and its collection
-- of arguments.  The least fixed point of (X ↦ ⟦ C ⟧ X) is the indexed
-- W-type given by C, and it contains closed first-order terms of the
-- multi-sorted algebra C.

-- We need to interpreting indexed containers on Setoids.
-- This definition is missing from the standard library v1.7.
-- It equips the sets (⟦ C ⟧ X) with an equivalence relation
-- induced by the one of the family $X$.

⟦_⟧s : (C : Container ℓᵒ ℓᵃ) (ξ : Setoid ℓᵐ ℓᵉ) → Setoid _ _

⟦ C ⟧s ξ .Carrier =
  ⟦ C ⟧ (Carrier ξ)

⟦ Op ▷ Ar ⟧s ξ ._≈_ (op , args) (op' , args') =
  Σ[ eq ∈ op ≡ op' ] EqArgs eq args args'
  where
  EqArgs : (eq : op ≡ op')
           (args   : (i : Ar op)   → ξ .Carrier)
           (args'  : (i : Ar op')  → ξ .Carrier)
         → Set _
  EqArgs refl args args' = (i : Ar op) → ξ ._≈_ (args i) (args' i)

⟦ Op ▷ Ar ⟧s ξ  .isEquivalence .IsEquivalence.refl
                        = refl , λ i → Setoid.refl   ξ
⟦ Op ▷ Ar ⟧s ξ  .isEquivalence .IsEquivalence.sym    (refl , g)
                        = refl , λ i → Setoid.sym    ξ (g i)
⟦ Op ▷ Ar ⟧s ξ  .isEquivalence .IsEquivalence.trans  (refl , g) (refl , h)
                        = refl , λ i → Setoid.trans  ξ (g i) (h i)

-- Multi-sorted algebras
-- =====================
--
-- A multi-sorted algebra is an indexed container.
--
-- * Sorts are indexes.
--
-- * Operators are commands/shapes.
--
-- * Arities/argument are responses/positions.
--
-- Closed terms (initial model) are given by the W type for a container,
-- renamed to μ here (for least fixed-point).

-- It is convenient to name the concept of signature, i.e. (Sort, Ops)
record Signature (ℓᵒ ℓᵃ : Level) : Set (suc (ℓᵒ ⊔ ℓᵃ)) where
  field
    Ops : Container ℓᵒ ℓᵃ

-- We assume a fixed signature.

module _ (Sig : Signature ℓᵒ ℓᵃ) where
  open Signature Sig
  open Container Ops renaming
    ( Shape   to  Op
    ; Position  to  Arity
    )

  variable
    op op'  : Op

  -- Models
  ---------

  -- A model is given by an interpretation (Den $s$) for each sort $s$
  -- plus an interpretation (den $o$) for each operator $o$.
  -- A model is also frequently known as an \emph{Algebra} for a
  -- signature; but as that terminology is too overloaded, it is
  -- avoided here.

  record SetModel ℓᵐ : Set (ℓᵒ ⊔ ℓᵃ ⊔ suc ℓᵐ) where
    field
      Den : Set ℓᵐ
      den : ⟦ Ops ⟧ Den → Den

  -- The setoid model requires operators to respect equality.
  -- The Func record packs a function (apply) with a proof (cong)
  -- that the function maps equals to equals.

  record SetoidModel ℓᵐ ℓᵉ : Set (ℓᵒ ⊔ ℓᵃ ⊔ suc (ℓᵐ ⊔ ℓᵉ)) where
    field
      Den  :  Setoid ℓᵐ ℓᵉ
      den  :  Func (⟦ Ops ⟧s Den) Den

  -- Terms
  -- =====

  -- To obtain terms with free variables, we add additional nullary
  -- operators, each representing a variable.
  --
  -- These are covered in the standard library FreeMonad module,
  -- albeit with the restriction that the operator and variable sets
  -- have the same size.

  Cxt : Set (suc ℓᵒ)
  Cxt = Set ℓᵒ

  variable
    Γ Δ : Cxt

  -- Terms with free variables in Var.

  module _ (Var : Cxt) where

    -- We keep the same sorts, but add a nullary operator for each variable.

    Ops⁺ : Container ℓᵒ ℓᵃ
    Ops⁺ = Ops ⋆C Var

    -- Terms with variables are then given by the W-type (named μ) for the extended container.

    Tm : Set _
    Tm = μ Ops⁺

    -- We define nice constructors for variables and operator application
    -- via pattern synonyms.
    -- Note that the $f$ in constructor var' is a function from the empty set,
    -- so it should be uniquely determined.  However, Agda's equality is
    -- more intensional and will not identify all functions from the empty set.
    -- Since we do not make use of the axiom of function extensionality,
    -- we sometimes have to consult the extensional equality of the
    -- function setoid.

    pattern _∙_ op args  = sup (inj₂ op , args)
    pattern var' x f     = sup (inj₁ x , f    )
    pattern var x        = var' x _

  -- Letter $t$ ranges over terms, and $\mathit{ts}$ over argument vectors.

  variable
    t t' t₁ t₂ t₃  :  Tm Γ
    ts ts'         :  (i : Arity op) → Tm Γ

  -- Parallel substitutions
  -------------------------

  -- A substitution from Δ to Γ holds a term in Γ for each variable in Δ.

  Sub : (Γ Δ : Cxt) → Set _
  Sub Γ Δ = (x : Δ) → Tm Γ

  -- Application of a substitution.

  _[_] : (t : Tm Δ) (σ : Sub Γ Δ) → Tm Γ
  (var x  )  [ σ ] = σ x
  (op ∙ ts)  [ σ ] = op ∙ λ i → ts i [ σ ]

  -- Letter $σ$ ranges over substitutions.

  variable
    σ σ' : Sub Γ Δ

  -- Interpretation of terms in a model
  -- ==================================

  -- Given an algebra $M$ of set-size $ℓ^m$ and equality-size $ℓ^e$,
  -- we define the interpretation of an $s$-sorted term $t$ as element
  -- of $M(s)$ according to an environment $ρ$ that maps each variable
  -- of sort $s'$ to an element of $M(s')$.

  module _ {M : SetoidModel ℓᵐ ℓᵉ} where
    open SetoidModel M

    -- Equality in $M$'s interpretation of sort $s$.

    _≃_ : Den .Carrier → Den .Carrier → Set _
    _≃_ = Den ._≈_

    -- An environment for Γ maps each variable $x : Γ(s)$ to an element of $M(s)$.
    -- Equality of environments is defined pointwise.

    Env : Cxt → Setoid _ _
    Env Γ .Carrier   = (x : Γ) → Den .Carrier
    Env Γ ._≈_ ρ ρ'  = (x : Γ) → ρ x ≃ ρ' x
    Env Γ .isEquivalence .IsEquivalence.refl        x = Den .Setoid.refl
    Env Γ .isEquivalence .IsEquivalence.sym       h x = Den .Setoid.sym   (h x)
    Env Γ .isEquivalence .IsEquivalence.trans  g  h x = Den .Setoid.trans (g x) (h x)

    -- Interpretation of terms is iteration on the W-type.
    -- The standard library offers `iter' (on sets), but we need this to be a Func (on setoids).

    ⦅_⦆ : (t : Tm Γ) → Func (Env Γ) Den
    ⦅ var x      ⦆ .apply  ρ     = ρ x
    ⦅ var x      ⦆ .cong   ρ=ρ'  = ρ=ρ' x
    ⦅ op ∙ args  ⦆ .apply  ρ     = den .apply  (op    , λ i → ⦅ args i ⦆ .apply ρ)
    ⦅ op ∙ args  ⦆ .cong   ρ=ρ'  = den .cong   (refl  , λ i → ⦅ args i ⦆ .cong ρ=ρ')

    -- An equality between two terms holds in a model
    -- if the two terms are equal under all valuations of their free variables.

    Equal : ∀ {Γ} (t t' : Tm Γ) → Set _
    Equal {Γ} t t' = ∀ (ρ : Env Γ .Carrier) → ⦅ t ⦆ .apply ρ ≃ ⦅ t' ⦆ .apply ρ

    -- This notion is an equivalence relation.

    isEquiv : IsEquivalence (Equal {Γ = Γ})
    isEquiv .IsEquivalence.refl  ρ       = Den .Setoid.refl
    isEquiv .IsEquivalence.sym   e ρ     = Den .Setoid.sym (e ρ)
    isEquiv .IsEquivalence.trans e e' ρ  = Den .Setoid.trans (e ρ) (e' ρ)

    -- Substitution lemma
    ---------------------

    -- Evaluation of a substitution gives an environment.

    ⦅_⦆s : Sub Γ Δ → Env Γ .Carrier → Env Δ .Carrier
    ⦅ σ ⦆s ρ x = ⦅ σ x ⦆ .apply ρ

    -- Substitution lemma: ⦅t[σ]⦆ρ ≃ ⦅t⦆⦅σ⦆ρ

    substitution : (t : Tm Δ) (σ : Sub Γ Δ) (ρ : Env Γ .Carrier) →
      ⦅ t [ σ ] ⦆ .apply ρ ≃ ⦅ t ⦆ .apply (⦅ σ ⦆s ρ)
    substitution (var x)    σ ρ = Den .Setoid.refl
    substitution (op ∙ ts)  σ ρ = den .cong (refl , λ i → substitution (ts i) σ ρ)

  -- Equations
  -- =========

  -- An equation is a pair $t ≐ t'$ of terms of the same sort in the same context.

  record Eq : Set (suc ℓᵒ ⊔ ℓᵃ) where
    constructor _≐_
    field
      {cxt}  : Set ℓᵒ
      lhs    : Tm cxt
      rhs    : Tm cxt

  -- Equation $t ≐ t'$ holding in model $M$.

  _⊧_ : (M : SetoidModel ℓᵐ ℓᵉ) (eq : Eq) → Set _
  M ⊧ (t ≐ t') = Equal {M = M} t t'

  -- Sets of equations are presented as collection E : I → Eq
  -- for some index set I : Set ℓⁱ.

  -- An entailment/consequence $E ⊃ t ≐ t'$ is valid
  -- if $t ≐ t'$ holds in all models that satify equations $E$.

  module _ {ℓᵐ ℓᵉ} where

    _⊃_ : (E : I → Eq) (eq : Eq) → Set _
    E ⊃ eq = ∀ (M : SetoidModel ℓᵐ ℓᵉ) → (∀ i → M ⊧ E i) → M ⊧ eq

  -- Derivations
  --------------

  -- Equalitional logic allows us to prove entailments via the
  -- inference rules for the judgment $E ⊢ Γ ▹ t ≡ t'$.
  -- This could be coined as equational theory over a given
  -- set of equations $E$.
  -- Relation $E ⊢ Γ ▹ \_ ≡ \_$ is the least congruence over the equations $E$.

  data _⊢_▹_≡_ {I : Set ℓⁱ}
    (E : I → Eq) : (Γ : Cxt) (t t' : Tm Γ) → Set (suc ℓᵒ ⊔ ℓᵃ ⊔ ℓⁱ) where

    hyp    :  ∀ i → let t ≐ t' = E i in
              E ⊢ _ ▹ t ≡ t'

    base   :  ∀ (x : Γ) {f f' : (i : ⊥) → Tm _} →
              E ⊢ Γ ▹ var' x f ≡ var' x f'

    app    :  (∀ i → E ⊢ Γ ▹ ts i ≡ ts' i) →
              E ⊢ Γ ▹ (op ∙ ts) ≡ (op ∙ ts')

    sub    :  E ⊢ Δ ▹ t ≡ t' →
              ∀ (σ : Sub Γ Δ) →
              E ⊢ Γ ▹ (t [ σ ]) ≡ (t' [ σ ])

    refl   :  ∀ (t : Tm Γ) →
              E ⊢ Γ ▹ t ≡ t

    sym    :  E ⊢ Γ ▹ t ≡ t' →
              E ⊢ Γ ▹ t' ≡ t

    trans  :  E ⊢ Γ ▹ t₁ ≡ t₂ →
              E ⊢ Γ ▹ t₂ ≡ t₃ →
              E ⊢ Γ ▹ t₁ ≡ t₃

  -- Soundness of the inference rules
  -----------------------------------

  -- We assume a model $M$ that validates all equations in $E$.

  module Soundness {I : Set ℓⁱ} (E : I → Eq) (M : SetoidModel ℓᵐ ℓᵉ)
    (V : ∀ i → M ⊧ E i) where
    open SetoidModel M

    -- In any model $M$ that satisfies the equations $E$,
    -- derived equality is actual equality.

    sound : E ⊢ Γ ▹ t ≡ t' → M ⊧ (t ≐ t')

    sound (hyp i)                        =  V i
    sound (app {op = op} es) ρ           =  den .cong (refl , λ i → sound (es i) ρ)
    sound (sub {t = t} {t' = t'} e σ) ρ  =  begin
      ⦅ t [ σ ]   ⦆ .apply ρ   ≈⟨ substitution {M = M} t σ ρ ⟩
      ⦅ t         ⦆ .apply ρ'  ≈⟨ sound e ρ' ⟩
      ⦅ t'        ⦆ .apply ρ'  ≈˘⟨ substitution {M = M} t' σ ρ ⟩
      ⦅ t' [ σ ]  ⦆ .apply ρ   ∎
      where
      open SetoidReasoning Den
      ρ' = ⦅ σ ⦆s ρ

    sound (base x {f} {f'})              =  isEquiv {M = M} .IsEquivalence.refl {var' x λ()}

    sound (refl t)                       =  isEquiv {M = M} .IsEquivalence.refl {t}
    sound (sym {t = t} {t' = t'} e)      =  isEquiv {M = M} .IsEquivalence.sym
                                            {x = t} {y = t'} (sound e)
    sound (trans  {t₁ = t₁} {t₂ = t₂}
                  {t₃ = t₃} e e')        =  isEquiv {M = M} .IsEquivalence.trans
                                            {i = t₁} {j = t₂} {k = t₃} (sound e) (sound e')

  -- Birkhoff's completeness theorem
  -- ===============================

  -- Birkhoff proved that any equation $t ≐ t'$ is derivable from $E$
  -- when it is valid in all models satisfying $E$.  His proof (for
  -- single-sorted algebras) is a blue print for many more
  -- completeness proofs.  They all proceed by constructing a
  -- universal model aka term model.  In our case, it is terms
  -- quotiented by derivable equality $E ⊢ Γ ▹ \_ ≡ \_$.  It then
  -- suffices to prove that this model satisfies all equations in $E$.

  -- Universal model
  ------------------

  -- A term model for $E$ and $Γ$ interprets sort $s$ by (Tm Γ s) quotiented by $E ⊢ Γ ▹ \_ ≡ \_$.

  module TermModel {I : Set ℓⁱ} (E : I → Eq) where
    open SetoidModel

    -- Tm Γ s quotiented by E⊢Γ▹·≡·.

    TmSetoid : Cxt → Setoid _ _
    TmSetoid Γ .Carrier                             = Tm Γ
    TmSetoid Γ ._≈_                                 = E ⊢ Γ ▹_≡_
    TmSetoid Γ .isEquivalence .IsEquivalence.refl   = refl _
    TmSetoid Γ .isEquivalence .IsEquivalence.sym    = sym
    TmSetoid Γ .isEquivalence .IsEquivalence.trans  = trans

    -- The interpretation of an operator is simply the operator.
    -- This works because $E⊢Γ▹\_≡\_$ is a congruence.

    tmInterp : ∀ {Γ} → Func (⟦ Ops ⟧s (TmSetoid Γ)) (TmSetoid Γ)
    tmInterp .apply (op , ts) = op ∙ ts
    tmInterp .cong (refl , h) = app h

    -- The term model per context Γ.

    M : Cxt → SetoidModel _ _
    M Γ .Den = TmSetoid Γ
    M Γ .den = tmInterp

    -- The identity substitution σ₀ maps variables to themselves.

    σ₀ : {Γ : Cxt} → Sub Γ Γ
    σ₀ x = var' x  λ()

    -- σ₀ acts indeed as identity.

    identity : (t : Tm Γ) → E ⊢ Γ ▹ t [ σ₀ ] ≡ t
    identity (var x)    = base x
    identity (op ∙ ts)  = app λ i → identity (ts i)

    -- Evaluation in the term model is substitution $E ⊢ Γ ▹ ⦅t⦆σ ≡ t[σ]$.
    -- This would even hold "up to the nose" if we had function extensionality.

    evaluation : (t : Tm Δ) (σ : Sub Γ Δ) → E ⊢ Γ ▹ (⦅_⦆ {M = M Γ} t .apply σ) ≡ (t [ σ ])
    evaluation (var x)    σ = refl (σ x)
    evaluation (op ∙ ts)  σ = app (λ i → evaluation (ts i) σ)

    -- The term model satisfies all the equations it started out with.

    satisfies : ∀ i → M Γ ⊧ E i
    satisfies i σ = begin
      ⦅ tₗ ⦆ .apply σ  ≈⟨ evaluation tₗ σ ⟩
      tₗ [ σ ]         ≈⟨ sub (hyp i) σ ⟩
      tᵣ [ σ ]         ≈˘⟨ evaluation tᵣ σ ⟩
      ⦅ tᵣ ⦆ .apply σ  ∎
      where
      open SetoidReasoning (TmSetoid _)
      tₗ  = E i .Eq.lhs
      tᵣ = E i .Eq.rhs

  -- Completeness
  ---------------

  -- Birkhoff's completeness theorem \citeyearpar{birkhoff:1935}:
  -- Any valid consequence is derivable in the equational theory.

  module Completeness {I : Set ℓⁱ} (E : I → Eq) {Γ} {t t' : Tm Γ} where
    open TermModel E

    completeness : E ⊃ (t ≐ t') → E ⊢ Γ ▹ t ≡ t'
    completeness V =     begin
      t                  ≈˘⟨ identity t ⟩
      t  [ σ₀ ]          ≈˘⟨ evaluation t σ₀ ⟩
      ⦅ t   ⦆ .apply σ₀  ≈⟨ V (M Γ) satisfies σ₀ ⟩
      ⦅ t'  ⦆ .apply σ₀  ≈⟨ evaluation t' σ₀ ⟩
      t' [ σ₀ ]          ≈⟨ identity t' ⟩
      t'                 ∎
      where open SetoidReasoning (TmSetoid Γ)

{- Q.E.D 2021-05-28 -}

-- -}
-- -}
-- -}
-- -}
-- -}
