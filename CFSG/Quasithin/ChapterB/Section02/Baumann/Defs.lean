module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Frattini

/-!
# Source data for Baumann's argument

These are the hypotheses (a)–(d) of Aschbacher–Smith B.2.18, printed
pp.80–81 of the combined manuscript of 1 March 2004. Hypothesis (e) is
kept separate: B.2.19 needs the preliminary conjugacy argument before it
can prove (e). The residual is the intersection of normal subgroups with
two-group quotient, and the Frattini term is the preimage of the actual
Frattini subgroup of `L/O₂(L)`.

The quantitative no-strong-offender condition tests every elementary image
of a subgroup of R, including images whose full inverse image is not
elementary. Thus it tests every elementary subgroup of R*. Its codimension
is the rank of the actual fixed-space quotient, expressed as a difference
of base-two logarithms of orders.
-/

namespace CFSG.Quasithin.ChapterB.BaumannArgument

open Stellmacher
variable {G : Type*} [Group G]

/-- The fixed-space codimension `m(V/C_V(A))` for an elementary V. -/
@[expose] public noncomputable def fixedCodim (V A : Subgroup G) : ℕ :=
  Nat.log 2 (Nat.card V) -
    Nat.log 2 (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)))

/-- The genuine action quotient map `G → G/C_G(V)`. -/
@[expose] public def actionMap (V : Subgroup G) [V.Normal] :
    G →* G ⧸ Subgroup.centralizer (V : Set G) :=
  QuotientGroup.mk' (Subgroup.centralizer (V : Set G))

/-- The subgroup `O_{2,Φ}(L)`, embedded in the common ambient group. -/
@[expose] public noncomputable def coreFrattini (L : Subgroup G) : Subgroup G :=
  ((frattini (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))).map L.subtype

/-- No elementary subgroup of R* has rank exceeding its fixed codimension.
Subgroups of R are allowed arbitrary kernels, so this tests all subgroups
of R*, not merely those with an elementary lift. -/
@[expose] public def NoStrongOffenders (V R : Subgroup G) [V.Normal] : Prop :=
  ∀ A : Subgroup G, A ≤ R → IsElementaryAbelian 2 (A.map (actionMap V)) →
    A.map (actionMap V) ≠ ⊥ →
    Nat.log 2 (Nat.card (A.map (actionMap V))) ≤ fixedCodim V A

/-- Conjugacy of a subgroup under a specified overgroup. The convention
`g*x*g⁻¹` does not change the family, since the conjugators form a group. -/
@[expose] public def conjugatesBy (H K : Subgroup G) : Set (Subgroup G) :=
  {D | ∃ g ∈ H, D = K.map (MulAut.conj g).toMonoidHom}

variable [Finite G] {ι : Type*} [Fintype ι]

/-- Exactly the setup and clauses (a)–(d) of B.2.18. V's normal elementary
structure is a typeclass argument of the source theorems. No conclusion,
normality of the generated group, or hypothesis (e) is included here. -/
public structure HypothesesAD (V R : Subgroup G) [V.Normal]
    (X : ι → Subgroup G) : Prop where
  R_two : IsPGroup 2 R
  V_le_R : V ≤ R
  core_le : (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤
    R ⊓ Subgroup.centralizer (V : Set G)
  normalizes : pResidual 2 G ≤
    Subgroup.normalizer (R ⊓ Subgroup.centralizer (V : Set G) : Set G)
  centralizer_le_frattini : pResidual 2 G ⊓ Subgroup.centralizer (V : Set G) ≤
    coreFrattini (pResidual 2 G)
  no_strong : NoStrongOffenders V R
  conjugate_into : ∀ i, ∃ l ∈ pResidual 2 G,
    (X i).map (MulAut.conj l).toMonoidHom ≤ R
  self_thompson : ∀ i, elementaryAbelianMaxJ (X i) = X i
  rank_eq : ∀ i, twoRank (X i) = twoRank R
  image_generation : (pResidual 2 G).map (actionMap V) ≤
    ⨆ i, (X i).map (actionMap V)
  codimension_sum : (∑ i, fixedCodim V (X i)) ≤ fixedCodim V (pResidual 2 G)

end CFSG.Quasithin.ChapterB.BaumannArgument
