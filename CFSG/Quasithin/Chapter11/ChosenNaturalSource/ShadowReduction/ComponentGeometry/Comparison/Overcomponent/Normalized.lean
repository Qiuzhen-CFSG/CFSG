module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Containment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection

/-!
# Normalization and a chosen module for the actual overcomponent

The point component is normalized by T. Unique C-component containment
inside JT, together with the source bound of two on component orbits,
therefore makes every local overcomponent J normal in JT. This excludes
the nonnormal alternative of 7.0.1 before any module classification.

For a proper maximal J with quasisimple two-core quotient, point movement
supplies faithful-local membership. The ambient source exclusions are
unchanged, so the original Hypothesis12.2.3 and an actual chosen Irr⁺
module can be constructed for J. The normalized 7.0.1 producer can thus
be reused on this new chosen module; it need not be reproved for an
unconnected abstract group or assumed from faithful membership.
Source: Aschbacher--Smith 11.4.2, printed p.776, using 1.2.1(3), 1.2.4
and 3.2.1, printed pp.504--505,579.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The actual point component is T-invariant by its conjugate-span definition. -/
theorem sylow_normalizes_point (h : EarlierGeometry E) :
    (T : Subgroup G) ≤ normalizer (E.Kz : Set G) :=
  h.sylow_le_pointCentralizer.trans (le_normalizer_conjugateSpanBy _ _)

/-- A local overcomponent inherits T-normalization from the point component
using unique containment in the literal group JT. -/
theorem sylow_normalizes_overcomponent (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hle : E.Kz ≤ J) :
    (T : Subgroup G) ≤ normalizer (J : Set G) := by
  have hlocal := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_, _, _, _, hsq⟩ := MainForward.localComponents_local_setup
    E.input.source.simpleQTKE T hlocal
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G) (J ⊔ (T : Subgroup G)) :=
    ⟨T.subtype le_sup_right, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]⟩
  obtain ⟨C, hC, _, hu⟩ := LocalGeometry.Components.exists_unique_normal_component
    hsq hs (hle.trans le_sup_left) h.point_mem_local_family (sylow_normalizes_point h)
  have he : J = C := hu J ⟨le_sup_left, hJ.1⟩ hle
  have hn : (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal := he.symm ▸ hC.2
  exact (show (T : Subgroup G) ≤ J ⊔ (T : Subgroup G) from le_sup_right).trans
    ((normal_subgroupOf_iff_le_normalizer (show J ≤ J ⊔ (T : Subgroup G) from
      le_sup_left)).mp hn)

/-- The actor L₀ of 7.0.1 is exactly J, so its fourth alternative is
impossible for this overcomponent. -/
theorem localOrbit_eq (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hle : E.Kz ≤ J) :
    Chapter3.Section02.localOrbit T J = J :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer J _ J le_rfl
    (sylow_normalizes_overcomponent h hJ hle)) (le_componentOrbit J _)

/-- All original source hypotheses transfer to the actual proper maximal
overcomponent; the ambient group and its exclusions are unchanged. -/
theorem source_hypotheses (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hlt : E.Kz < J)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J where
  simpleQTKE := E.input.source.simpleQTKE
  maximal_faithful := ⟨hJ, faithful h hJ.1 hlt⟩
  quasisimple := hq
  no_rankTwo := E.input.source.no_rankTwo
  no_M22 := E.input.source.no_M22
  no_M23 := E.input.source.no_M23
  no_J4 := E.input.source.no_J4

/-- The chosen module is on R₂(JT) for the very same overcomponent J.
Its T-orbit actor equals J, excluding the fourth alternative of 7.0.1. -/
theorem exists_chosenModule (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hlt : E.Kz < J)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  have hs := source_hypotheses h hJ hlt hq
  exact ⟨hs, hs.toHypothesis1221.exists_chosen_of_normalizes
    (sylow_normalizes_overcomponent h hJ.1 hlt.le)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent
