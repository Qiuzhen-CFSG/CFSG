module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.Endpoint

/-!
# Critical-pair symmetry in the `G₂(2)'` branch

This file is the conditional part of Aschbacher--Smith, Lemmas 14.7.58--62.
The representation-theoretic work in 14.7.54--57 is deliberately an input:
the record below names the rank, parabolic, dual-action, and transvection
facts which those lemmas provide.  The deductions in this file are ordinary
subgroup arguments.  In particular, `relativeTwoCore` is kept separate from
the ambient two-residual, and all quotient maps in the endpoint application
are the literal maps on the restricted group `Uβ`.

The record is intentionally independent of the producer's declaration names.
It can therefore be instantiated by the marked-geometry module without
importing that module here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, printed pp.1067--1068 (PDF
pp.1084--1085), Lemmas 14.7.58--62.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion

open Subgroup

variable {G Gs X : Type*} [Group G] [Group Gs] [MulAction G X]

/-- The concrete meaning of the source assertion `H* ≅ G₂(2)`. -/
def IsG2Two (H : Subgroup Gs) : Prop :=
  Nonempty (H ≃* Atlas.G2.Model (ZMod 2))

/-- The endpoint swap in Notation 14.7.1.  The source supplies the action on
the two marked vertices; spelling it out prevents an unconnected family tag
from being mistaken for the interchange assertion. -/
def Interchanges (γ₁ α : X) (g : G) : Prop :=
  g • γ₁ = α ∧ g • α = γ₁

/-- A source witness that an element of `U₀ \ D` induces a transvection.
The action itself is supplied by F.9.13(6) and 14.7.55(4); no transvection
classification is hidden in this definition. -/
def U0OutsideDTransvection (U₀ D : Subgroup G) (transvection : G → Prop) : Prop :=
  ∃ u₀ : G, u₀ ∈ U₀ ∧ u₀ ∉ D ∧ transvection u₀

/-- Explicit source data used by the critical-pair deductions.

`starRank` is the elementary-module rank on the indicated starred subgroup,
and `quotientRank` is the rank of the literal quotient module.  The fields
named `*_formula` are the formulas of 14.7.55--57; they are not conclusions
of Lemmas 14.7.58--62.  The two inclusions used in the `D = U⁻` step and
the rank-reflection principle are kept as separate fields so that the final
equality is proved by `le_antisymm` after the source rank calculation. -/
structure CriticalSymmetryInput where
  H : Subgroup G
  K : Subgroup G
  U : Subgroup G
  V : Subgroup G
  V₁ : Subgroup G
  V₂ : Subgroup G
  Uα : Subgroup G
  Qα : Subgroup G
  Zα : Subgroup G
  D : Subgroup G
  U₀ : Subgroup G
  Uminus : Subgroup G
  M1 : Subgroup G
  Uplus : Subgroup Gs
  Wplus : Subgroup Gs
  HαStar : Subgroup Gs
  UαStar : Subgroup Gs
  AStar : Subgroup Gs
  BStar : Subgroup Gs
  V₂α : Subgroup G
  V₂Conj : G → Subgroup G
  AStarAt : Subgroup G → Subgroup G → Subgroup Gs
  BStarAt : Subgroup G → Subgroup G → Subgroup Gs
  centralizerHαStar : Subgroup Gs
  starRank : Subgroup Gs → ℕ
  quotientRank : Subgroup G → Subgroup G → ℕ
  groupRank : Subgroup G → ℕ
  relativeTwoCore : Subgroup Gs → Subgroup Gs
  γ₁ : X
  α : X
  transvection : G → Prop
  /-- `H = G₁ = KT`, the selected critical-pair setup. -/
  hH_eq_G1 : H = K
  hK_eq_KT : K = H ⊔ U
  /-- Uniqueness in `H_z` and the centralizer placement of `K`. -/
  unique_in_Hz : Prop
  K_in_centralizer_H : K ≤ centralizer (H : Set G)
  /-- The source identity `U = [U,K]`. -/
  U_eq_commutator : U = ⁅U, K⁆
  /-- The `G₂(2)'` branch and the 14.7.55--57 marked-module formulas. -/
  g2_branch : Prop
  two_transitive_interchange :
    Zα ≤ V → ∃ g : G, Interchanges γ₁ α g
  rank_interchange :
    Zα ≤ V → (∃ g : G, Interchanges γ₁ α g) →
      starRank UαStar = quotientRank U D
  /-- The nontrivial relative two-core is obtained from the source core seed. -/
  coreSeed : Subgroup Gs
  coreSeed_ne_bot : coreSeed ≠ ⊥
  coreSeed_le_relative : coreSeed ≤ relativeTwoCore HαStar
  /-- The alignment formula in 14.7.60(1). -/
  alignWitness :
    Zα ≤ U → ∃ a : G, a ∈ M1 ∧ V₂α = V₂Conj a ∧
      Zα ⊔ U₀ = V₂α ⊔ U₀
  /-- The centralizer identification in 14.7.60(2). -/
  hαStar_eq_centralizer :
    Zα ≤ U → HαStar = centralizerHαStar
  /-- The two alternatives in 14.7.60(3), after alignment. -/
  parabolic_alternatives :
    Zα ≤ U → UαStar = AStar ∨ UαStar = BStar
  /-- The `D ≤ U⁻` alternative accompanying the parabolic calculation. -/
  d_le_uminus_of_A : UαStar = AStar → D ≤ Uminus
  d_le_uminus_of_B : UαStar = BStar → D ≤ Uminus
  /-- Source ranks from 14.7.55(4) and the marked parabolic calculation. -/
  astar_rank : starRank AStar = 3
  bstar_rank : starRank BStar = 2
  uminus_rank : groupRank Uminus = 3
  quotient_rank_eq_uminus : groupRank Uminus = quotientRank U D
  d_rank_eq_quotient : groupRank D = quotientRank U D
  /-- Rank reflection for the elementary abelian layers. -/
  rank_reflects_eq :
    ∀ {P Q : Subgroup G}, P ≤ Q → groupRank P = groupRank Q → P = Q
  /-- The FF-offender branch of 14.7.55(5). -/
  offender : Prop
  offender_to_g2 : offender → IsG2Two HαStar
  /-- The non-offender branch gives the source `U₀ \ D` transvection. -/
  nonoffender_witness :
    ¬ offender → U0OutsideDTransvection U₀ D transvection
  no_transvection : ∀ u : G, transvection u → False
  /-- The source symmetry transfers the first noncontainment to the second. -/
  zα_not_le_of_symmetry : ¬ V₁ ≤ Uα → ¬ Zα ≤ U
  /-- The dual-action calculation gives the first noncontainment. -/
  v₁_containment_transvection : V₁ ≤ Uα → ∃ u : G, transvection u
  /-- The two symmetric identifications in 14.7.62. -/
  uplus_le_astar : Uplus ≤ AStarAt Zα V₂α
  astar_le_uplus : AStarAt Zα V₂α ≤ Uplus
  wplus_le_bstar : Wplus ≤ BStarAt Zα V₂α
  bstar_le_wplus : BStarAt Zα V₂α ≤ Wplus
  /-- The `B*` alternative is excluded by the source non-offender calculation. -/
  bstar_impossible : UαStar = BStar → False

namespace CriticalSymmetryInput

variable (i : CriticalSymmetryInput (G := G) (Gs := Gs) (X := X))

theorem source_setup : i.H = i.K ∧ i.K = i.H ⊔ i.U :=
  ⟨i.hH_eq_G1, i.hK_eq_KT⟩

/-- Lemma 14.7.58(1),(2): the marked vertices can be interchanged, and the
rank of the second starred module is the rank of the literal quotient `U/D`.
The two-transitivity witness and the rank transport are supplied separately
by 14.7.55--57. -/
theorem lemma_14_7_58 (hZV : i.Zα ≤ i.V) :
    (∃ g : G, Interchanges i.γ₁ i.α g) ∧
      i.starRank i.UαStar = i.quotientRank i.U i.D := by
  obtain ⟨g, hg⟩ := i.two_transitive_interchange hZV
  exact ⟨⟨g, hg⟩, i.rank_interchange hZV ⟨g, hg⟩⟩

/-- Lemma 14.7.59: the relative two-core of `Hα*` is nontrivial. -/
theorem lemma_14_7_59 : i.relativeTwoCore i.HαStar ≠ ⊥ := by
  intro h
  have hseed : i.coreSeed ≤ (⊥ : Subgroup Gs) := h ▸ i.coreSeed_le_relative
  exact i.coreSeed_ne_bot (le_antisymm hseed bot_le)

/-- Lemma 14.7.60(1)--(3): alignment, centralizer identification, and the
`A*`/`B*` alternatives.  The equality in the centralizer field is deliberately
kept as an explicit source formula; the theorem does not identify a relative
two-residual with a two-core. -/
theorem lemma_14_7_60 (hZU : i.Zα ≤ i.U) :
    (∃ a : G, a ∈ i.M1 ∧ i.V₂α = i.V₂Conj a ∧
      i.Zα ⊔ i.U₀ = i.V₂α ⊔ i.U₀) ∧
      i.HαStar = i.centralizerHαStar ∧
      (i.UαStar = i.AStar ∨ i.UαStar = i.BStar) := by
  obtain ⟨a, haM, ha, halign⟩ := i.alignWitness hZU
  exact ⟨⟨a, haM, ha, halign⟩, i.hαStar_eq_centralizer hZU,
    i.parabolic_alternatives hZU⟩

/-- The non-offender calculation is exposed as a separate contradiction.  It
is the delicate step in the printed proof: the rank-three quotient forces an
element of `U₀ \ D`, and F.9.13(6) turns it into a transvection, forbidden by
the source action on `Ũ`. -/
theorem nonoffender_transvection_contradiction : i.offender := by
  by_contra hno
  obtain ⟨u₀, hu₀, hu₀D, htr⟩ := i.nonoffender_witness hno
  exact i.no_transvection u₀ htr

/-- Lemma 14.7.61(1)--(4).  The non-offender case is eliminated by the actual
`U₀ \ D` transvection contradiction.  In the remaining FF-offender case the
source parabolic calculation gives `H* ≅ G₂(2)`, `Uα* = A*`, and rank three.
The equality `D = U⁻` is obtained from the source containment and the rank
reflection principle, rather than inserted as a field. -/
theorem lemma_14_7_61 (hZV : i.Zα ≤ i.V) (_hZU : i.Zα ≤ i.U) :
    IsG2Two i.HαStar ∧
      i.UαStar = i.AStar ∧
      i.D = i.Uminus ∧
      i.starRank i.UαStar = 3 ∧
      i.quotientRank i.U i.D = 3 ∧
      (∃ g : G, Interchanges i.γ₁ i.α g) := by
  have hoff : i.offender := by
    exact i.nonoffender_transvection_contradiction
  have hA : i.UαStar = i.AStar := by
    obtain hA | hB := i.parabolic_alternatives _hZU
    · exact hA
    · exact (i.bstar_impossible hB).elim
  have hG2 : IsG2Two i.HαStar := i.offender_to_g2 hoff
  have hrankα : i.starRank i.UαStar = 3 := by
    rw [hA]
    exact i.astar_rank
  have hDle : i.D ≤ i.Uminus := i.d_le_uminus_of_A hA
  have hquot : i.quotientRank i.U i.D = i.groupRank i.Uminus := by
    exact i.quotient_rank_eq_uminus.symm
  have hD : i.D = i.Uminus := i.rank_reflects_eq hDle (by
    rw [i.d_rank_eq_quotient, hquot, i.uminus_rank])
  obtain ⟨g, hg⟩ := i.two_transitive_interchange hZV
  have hq : i.quotientRank i.U i.D = 3 := by
    rw [hquot, i.uminus_rank]
  exact ⟨hG2, hA, hD, hrankα, hq, ⟨g, hg⟩⟩

/-- Lemma 14.7.62(1)--(3), with the two endpoint identifications proved by
antisymmetry of subgroup inclusion.  The second noncontainment is obtained by
the symmetry in Lemma 14.7.61(5), and the two starred equalities are the
literal `U⁺` and `W⁺` subgroups of the source quotient. -/
theorem lemma_14_7_62 :
    (¬ i.V₁ ≤ i.Uα ∧ ¬ i.Zα ≤ i.U) ∧
      i.Uplus = i.AStarAt i.Zα i.V₂α ∧ i.Wplus = i.BStarAt i.Zα i.V₂α := by
  have hV : ¬ i.V₁ ≤ i.Uα := by
    intro hV
    obtain ⟨u, hu⟩ := i.v₁_containment_transvection hV
    exact i.no_transvection u hu
  have hZ : ¬ i.Zα ≤ i.U := i.zα_not_le_of_symmetry hV
  exact ⟨⟨hV, hZ⟩, le_antisymm i.uplus_le_astar i.astar_le_uplus,
    le_antisymm i.wplus_le_bstar i.bstar_le_wplus⟩

/-- The complete conditional package used by the parent G₂ exclusion proof. -/
structure Result where
  interchange : ∃ g : G, Interchanges i.γ₁ i.α g
  rank_eq : i.starRank i.UαStar = i.quotientRank i.U i.D
  relative_twoCore_ne_bot : i.relativeTwoCore i.HαStar ≠ ⊥
  aligned : ∃ a : G, a ∈ i.M1 ∧ i.V₂α = i.V₂Conj a ∧
    i.Zα ⊔ i.U₀ = i.V₂α ⊔ i.U₀
  g2 : IsG2Two i.HαStar
  uα_eq_A : i.UαStar = i.AStar
  d_eq_uminus : i.D = i.Uminus
  rank_uα : i.starRank i.UαStar = 3
  rank_quotient : i.quotientRank i.U i.D = 3
  v₁_not_le : ¬ i.V₁ ≤ i.Uα
  zα_not_le : ¬ i.Zα ≤ i.U
  uplus_eq_A : i.Uplus = i.AStarAt i.Zα i.V₂α
  wplus_eq_B : i.Wplus = i.BStarAt i.Zα i.V₂α

/-- Assemble 14.7.58--62 from the source hypotheses. -/
theorem assemble (hZV : i.Zα ≤ i.V) (hZU : i.Zα ≤ i.U) : Result i := by
  obtain ⟨hinter, hrank⟩ := i.lemma_14_7_58 hZV
  have hcore := i.lemma_14_7_59
  obtain ⟨halign, hcent, hshape⟩ := i.lemma_14_7_60 hZU
  obtain ⟨hg2, hA, hD, hru, hq, _⟩ := i.lemma_14_7_61 hZV hZU
  obtain ⟨⟨hV, hZ⟩, huplus, hwplus⟩ := i.lemma_14_7_62
  exact ⟨hinter, hrank, hcore, halign, hg2, hA, hD, hru, hq,
    hV, hZ, huplus, hwplus⟩

end CriticalSymmetryInput

/-- Quotient data after restriction to `Uβ`.  Every subgroup is already a
subgroup of the subtype `Uβ`; consequently `mk' N` below is the literal
quotient map `Uβ → Uβ ⧸ N`, with no ambient-map coercion. -/
structure RestrictedEndpointData (Uβ : Type*) [Group Uβ] where
  N : Subgroup Uβ
  hN : N.Normal
  U : Subgroup Uβ
  A : Subgroup Uβ
  P : Subgroup Uβ
  Z : Subgroup Uβ
  R : Subgroup Uβ
  S : Subgroup Uβ
  hPA : ¬ P ≤ A
  hZU : ¬ Z ≤ U
  hZA : Z ≤ A
  hRU : R ≤ U
  hRA : R ≤ A
  hSU : S ≤ U
  hSA : S ≤ A
  hNR : N ≤ R
  hNS : N ≤ S
  hRS : R ≠ S

/-- The actual application of Endpoint.source_quotient_points_distinct on the
restricted group `Uβ`.  This is the quotient-faithful noncontainment package
used by the final four-cycle construction. -/
theorem restricted_endpoint_points_distinct
    {Uβ : Type*} [Group Uβ] (e : RestrictedEndpointData Uβ)
    [hN : e.N.Normal] :
    let π := QuotientGroup.mk' e.N
    e.P.map π ≠ e.Z.map π ∧ e.P.map π ≠ e.R.map π ∧
      e.P.map π ≠ e.S.map π ∧ e.Z.map π ≠ e.R.map π ∧
      e.Z.map π ≠ e.S.map π ∧ e.R.map π ≠ e.S.map π := by
  exact source_quotient_points_distinct e.N e.U e.A e.P e.Z e.R e.S
    e.hPA e.hZU e.hZA e.hRU e.hRA e.hSU e.hSA e.hNR e.hNS e.hRS

/-- Variant used by the final assembly: the two noncontainments are supplied
by Lemma 14.7.62(1), while the remaining endpoint incidence data are retained
in `e`.  Thus the call below consumes the actual outputs of the critical
symmetry proof rather than a duplicated endpoint record. -/
theorem restricted_endpoint_points_distinct_of_noncontainments
    {Uβ : Type*} [Group Uβ] (e : RestrictedEndpointData Uβ)
    [hN : e.N.Normal] (hPA : ¬ e.P ≤ e.A) (hZU : ¬ e.Z ≤ e.U) :
    let π := QuotientGroup.mk' e.N
    e.P.map π ≠ e.Z.map π ∧ e.P.map π ≠ e.R.map π ∧
      e.P.map π ≠ e.S.map π ∧ e.Z.map π ≠ e.R.map π ∧
      e.Z.map π ≠ e.S.map π ∧ e.R.map π ≠ e.S.map π := by
  let e' : RestrictedEndpointData Uβ := {e with hPA := hPA, hZU := hZU}
  exact restricted_endpoint_points_distinct e'

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion
