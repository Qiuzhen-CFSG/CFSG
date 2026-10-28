module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.MinimalLocal
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.OffenderLifts
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting.Basic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.RankTwoAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic

/-!
# Interfaces for the contained-offender component argument

`LocalInput` records the earlier local statements used in the component
argument; `PlacedInput` adds a best subgroup that the route constructs inside
an endpoint. In particular neither record asks for best status of the whole
endpoint, solvability of `M ∩ H`, a generated component layer, or a component.
`OutsideComponent` is the output to be constructed by exhaustive B.5.6 analysis.

These are conditional interfaces, not assertions of source theorems. The
extraspecial alternative, its residual, the theta and normalizer identities,
and the seed action must come from the earlier source hypotheses. The
contained best subgroup comes from `exists_containedBest` and compatible
conjugation. Once one outside component has been constructed, minimality
proves the replacement equality and (j) internally below.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(b), (h)–(j), printed pp.1143–1144; B.5.3–6, printed pp.104–105.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup Representation.BinaryOffender ComponentReduction
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G]

/-- Earlier local hypotheses needed to select a component. All cores are
relative to H, and the module is literally the Z_S-conjugate span modulo Z. -/
structure LocalInput (κ : GroupClass.{u}) (H M Y V Y0 T ZS Z : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)] where
  extraspecial : CosetSetup.ExtraspecialLocal.ExtraspecialCase M Y V
  residual : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G))
  sqtk : IsSQTK κ H
  base_le : Y0 ⊔ T ≤ H
  t_le_m : T ≤ M
  theta_eq : theta (M ⊓ H) = Y0
  normalizer_eq : normalizer (Y0 : Set G) = M
  core_le_m : localTwoCore H ≤ M
  seed_le : ZS ≤ V
  line_le_seed : Z ≤ ZS
  seed_centralized : Y0 ≤ centralizer (ZS : Set G)
  seed_normalizer : normalizer (ZS : Set G) ≤ M
  action : SectionAction H (localSpan ZS H) Z

/-- The best actor may be a proper subgroup of the elementary endpoint E.
Its lift and star image are kept distinct from E throughout. -/
structure PlacedInput (κ : GroupClass.{u}) (H M Y V Y0 T ZS Z E : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)] extends LocalInput κ H M Y V Y0 T ZS Z where
  selected : ContainedBest H (localSpan ZS H) Z E action
  actor_core : starImage H selected.carrier ≤
    (starImage H Y0 ⊔ starImage H T).pCoreIn 2

/-- Sufficient component output for the alternate route. It does not assert
that the initial span equals its C-component product. -/
structure OutsideComponent (H M Y0 A L : Subgroup G) : Prop where
  le_span : L ≤ localSpan A H
  component : (L.subgroupOf (localSpan A H)).IsCComponent
  quasisimple : Theory.GroupTheory.IsQuasisimple (starImage H L)
  orbit_bound : (Set.range fun h : H ⧸ pCore 2 H =>
    (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2
  outside : ¬ L ≤ M
  commutator_eq : L = ⁅L, Y0⁆

namespace LocalInput
variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : LocalInput κ H M Y V Y0 T ZS Z)
include d

/-- Two-perfectness also follows from the proved theta identity. -/
theorem twoPerfect [Finite G] : IsPPerfect 2 Y0 := by
  rw [← d.theta_eq]
  exact ComponentIntersection.theta_isPPerfect (M ⊓ H)

/-- Only Y_0, not the whole intersection M ∩ H, is asserted solvable. -/
theorem residual_solvable [Finite G] : Group.IsSolvable Y0 := by
  apply FactorGeneration.ClassificationCases.PerfectLifting.Y0_solvable_of_extraspecial
    M Y V Y0 d.extraspecial
  rw [d.residual]
  exact (map_subtype_le _).trans inf_le_left

/-- The fixed-seed input to the solvable-plane elimination is obtained from
ambient conjugation under the actual SectionAction. -/
theorem seed_fixed : ∀ z : ZS,
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
      ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∈
        fixedSpace d.action.representation (starImage H Y0) := by
  intro z a
  obtain ⟨y, hy, he⟩ := a.property
  change d.action.representation (a : H ⧸ pCore 2 H) _ = _
  rw [← he, d.action.on_representatives]
  congr 2
  apply Subtype.ext
  have hc := mem_centralizer_iff.mp (d.seed_centralized hy) z z.property
  change (z : G) * (y : G) = (y : G) * z at hc
  change (y : G) * z * (y : G)⁻¹ = z
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

end LocalInput

namespace PlacedInput
variable {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- The solvable-plane alternative is eliminated with the contained actor.
Only the exhaustive extraction of a factor remains a B.5.6 obligation. -/
theorem no_solvableStarFactor [Finite G]
    (F : FactorGeneration.SolvableStarFactor H ZS Z d.selected.carrier d.action) : False :=
  F.eliminate M Y0 T d.line_le_seed d.selected.le_local (le_sup_left.trans d.base_le)
    d.toLocalInput.twoPerfect d.normalizer_eq d.core_le_m d.theta_eq d.actor_core
    d.toLocalInput.seed_fixed d.seed_normalizer

end PlacedInput

namespace OutsideComponent
variable {H M Y0 A L : Subgroup G} (c : OutsideComponent H M Y0 A L)
include c

/-- Relative component membership passes through the normal conjugate span. -/
theorem in_local (hAH : A ≤ H) : (L.subgroupOf H).IsCComponent :=
  localSpan_component_isCComponent A H L hAH c.le_span c.component

/-- The equality H = <L^T>Y_0T and universal solvable control follow from
one constructed outside component. No new action is selected in this step. -/
theorem minimal_reduction [Finite G] {T upper : Subgroup G}
    (d : MinimalLocal Y0 T M upper H) (hQT : localTwoCore H ≤ T) (hAH : A ≤ H) :
    H = reducedOvergroup L Y0 T ∧
      ∀ K : Subgroup G, Group.IsSolvable K → Y0 ⊔ T ≤ K → K ≤ H → K ≤ M ⊓ H := by
  have hLH : L ≤ H := c.le_span.trans (conjugateSpanBy_le_self hAH)
  exact ⟨(d.reducedOvergroup_eq hQT hLH c.outside).symm,
    fun K hsol hbase hKH => d.solvable_overgroup_le hQT
      (MinimalLocal.not_solvable_of_component (c.in_local hAH)) K hsol hbase hKH⟩

end OutsideComponent
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
