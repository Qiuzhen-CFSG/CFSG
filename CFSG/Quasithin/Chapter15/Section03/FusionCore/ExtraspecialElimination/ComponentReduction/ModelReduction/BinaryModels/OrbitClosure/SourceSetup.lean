module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.CubicControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.LocalSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.OffenderTransport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.Quasithin.Rank

/-!
# Source hypotheses and the exact component-orbit alternative

The replacement in 15.3.49 retains the actual section action, the two
quadratic best offenders and their selected conjugate, component generation
and commutator generation in (i), universal solvable control (j), and (k).
In particular the selected component is only relatively subnormal in H.

The source SQTK condition descends through O₂(H) by coprime rank lifting.
The Sylow intersection and its star image are derived before applying the
universal 1.2.1(3) alternative. Its nonnormal case retains both the exact
normalizer index and actual model isomorphisms. Closure equality is an
output in the normal case, never a field of the source input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144 and Proposition 1.2.1(3), printed p.504.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The local source inputs after (k), with no component-orbit conclusion. -/
structure SourceSetup (κ : GroupClass.{u}) (H M Y L T ZS Z A : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)] where
  control : LocalControl H M Y T
  sqtk : IsSQTK κ H
  replacement : H = reducedOvergroup L Y T
  action : SectionAction H (localSpan ZS H) Z
  ugamma : Subgroup G
  vgamma : Subgroup G
  ugamma_le : ugamma ≤ vgamma
  vgamma_le : vgamma ≤ H
  ugamma_best : IsBestOffender action.representation (starImage H ugamma)
  ugamma_quadratic : IsQuadratic action.representation (starImage H ugamma)
  vgamma_best : IsBestOffender action.representation (starImage H vgamma)
  vgamma_quadratic : IsQuadratic action.representation (starImage H vgamma)
  selected : ∃ h : H, A = vgamma.map (MulAut.conj (h : G)).toMonoidHom
  actor_le : A ≤ H
  actor_core : starImage H A ≤
    (pCore 2 ↥(starImage H Y ⊔ starImage H T)).map
      (starImage H Y ⊔ starImage H T).subtype
  component_le : L ≤ localSpan A H
  component : (L.subgroupOf (localSpan A H)).IsCComponent
  component_generation :
    (cComponentLayer (localSpan A H)).map (localSpan A H).subtype = localSpan A H
  component_action : ∀ C : Subgroup G, C ≤ localSpan A H →
    (C.subgroupOf (localSpan A H)).IsCComponent → C = ⁅C, Y⁆
  y_le_closure : Y ≤ localSpan L T

/-- The exact universal input used by the published quotient proof of 1.2.1(3). -/
def EarlierOrbitAlternative (κ : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSQTK κ X → pCore 2 X = ⊥ →
    ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
        Section02.NonnormalCComponentModel B

namespace SourceSetup
variable {κ : GroupClass.{u}} {H M Y L T ZS Z A : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y L T ZS Z A)

include d

omit [Finite G] in
theorem component_le_H : L ≤ H :=
  d.component_le.trans (conjugateSpanBy_le_self d.actor_le)

omit [Finite G] in
theorem component_in_H : (L.subgroupOf H).IsCComponent :=
  localSpan_component_isCComponent A H L d.actor_le d.component_le d.component

omit [Finite G] in
theorem component_subnormal : (L.subgroupOf H).IsSubnormal :=
  d.component_in_H.subnormal

omit [Finite G] in
theorem commutator_eq : L = ⁅L, Y⁆ :=
  d.component_action L d.component_le d.component

omit [Finite G] in
/-- Conjugation transports both the full best-offender comparison and quadraticity. -/
theorem selected_offender :
    IsBestOffender d.action.representation (starImage H A) ∧
      IsQuadratic d.action.representation (starImage H A) := by
  obtain ⟨h, hA⟩ := d.selected
  simpa only [hA] using quadratic_bestOffender_conjugate H (localSpan ZS H) Z d.vgamma
    d.action d.vgamma_le h d.vgamma_best d.vgamma_quadratic

/-- The quotient SQTK premise is derived from the source local group. -/
theorem quotient_sqtk : IsSQTK κ (H ⧸ pCore 2 H) := by
  refine ⟨?_, d.sqtk.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _
    pCore_isPGroup).trans (d.sqtk.stronglyQuasithin p hp ho)

/-- The literal T ∩ L is Sylow before any normality assertion about L. -/
theorem sylow_sections :
    IsSylowIn 2 (T ⊓ L) L ∧
      IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L) :=
  component_inter_sylow H T L d.control.sylow d.component_le_H d.component_in_H

omit [Finite G] in
/-- Relative normality collapses the T-conjugate span. -/
theorem closure_eq_of_normal (hn : (L.subgroupOf H).Normal) : localSpan L T = L := by
  have hTH : T ≤ H := (isSylowIn_iff.mp d.control.sylow).2.1
  exact le_antisymm (conjugateSpanBy_le le_rfl
    (hTH.trans ((normal_subgroupOf_iff_le_normalizer d.component_le_H).mp hn)))
    (le_conjugateSpanBy L T)

omit [Finite G] in
/-- Once the orbit has collapsed, normality is relative to the replacement H. -/
theorem normal_and_normalized_of_closure_eq (he : localSpan L T = L) :
    (L.subgroupOf H).Normal ∧ T ≤ normalizer (L : Set G) := by
  have hn := componentClosure_normal_in_replacement L Y T
    (le_normalizer_iff_commutator_le_left.mpr d.commutator_eq.ge) d.control.normalizes
  rw [← d.replacement, he] at hn
  exact ⟨hn, he ▸ le_normalizer_conjugateSpanBy L T⟩

/-- A nontrivial orbit has the exact four-model quotient alternative and index two.
The intrinsic quotient is transported by its actual multiplicative equivalence. -/
theorem nonnormal_alternative (earlier : EarlierOrbitAlternative κ)
    (hne : localSpan L T ≠ L) :
    (normalizer (L.subgroupOf H : Set H)).index = 2 ∧
      Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) := by
  rcases Section02.proposition_1_2_1_three_index_of_A_3_8 earlier
    d.quotient_sqtk d.component_in_H with hn | ⟨hi, hm⟩
  · exact (hne (d.closure_eq_of_normal hn)).elim
  · let e := subgroupOfEquivOfLe d.component_le_H
    let eqv := QuotientGroup.congr (pCore 2 (L.subgroupOf H)) (pCore 2 L) e
      (pCore_map_iso 2 e)
    exact ⟨hi, hm.of_mulEquiv eqv.symm⟩

end SourceSetup
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
