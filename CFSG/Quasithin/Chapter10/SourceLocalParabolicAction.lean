module
public import CFSG.Quasithin.Chapter10.SourceLocalThompsonControl
public import CFSG.Quasithin.Chapter10.SourceA5MinimalParabolic

/-!
# The Chapter 10 parabolic alternatives from the local module

Apply E.2.3 to the actual reduced local FSU module. Its linear alternative
gives a Sylow Baumann subgroup and hence normalizer control by 3.1.1.
When J(T) centralizes the module, local Thompson control gives the same
bound. Thus the original marked symmetric-five alternative is the only
remaining case, without any full/local-module equality premise.

For an actual nonnormal A₅ component the earlier minimal-parabolic theorem
discharges the other premise. This is a source step in 10.2.1, retaining
the original group, module, quotient map, and marked exchanging element.
Source: Aschbacher–Smith, 10.1.2(6), 10.2.1, and E.2.3,
combined manuscript of 1 March 2004, printed pp.742–743,216–217.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

/-- The exact E.2.3 alternatives need only the original minimal parabolic. -/
theorem source_local_baumann_normalizer_or_five_action
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∨
      SourceFiveAction D := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)
  · exact Or.inl (source_local_baumann_normalizer_le_of_centralizes D hJ)
  have hmove : ¬ elementaryAbelianMaxJ (S : Subgroup H) ≤ centralizer (U : Set H) := by
    intro hc
    apply hJ
    have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le le_sup_right)
    rw [← hjmap]
    rintro g ⟨j, hj, rfl⟩ z hz
    exact congrArg H.subtype (hc hj
      ⟨z, (D.module_le_core.trans (pCoreIn_le 2 H)) hz⟩ hz)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  rcases source_linear_conclusions_or_symmetric_five
    (D.local_internal_module hu).sqtk S hP U hU hmove with hs | hf
  · apply Or.inl
    have huniq : Order.HasUniqueMaximalOver (T : Subgroup G) H := by
      have hh := hasUniqueMaximalOver_map_subtype
        ((ChapterB.isMinimalParabolicOver_iff S ⊤).mp hP).1
      have he : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
        map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
      exact he ▸ hh
    apply source_baumann_normalizer_le_of_orbit_sylow D huniq
    have hbmap : (ChapterB.baumann (S : Subgroup H)).map H.subtype =
        ChapterB.baumann (T : Subgroup G) := by
      have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
      change (ChapterB.baumann (S : Subgroup H)).map H.subtype =
        ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
      exact he.trans (congrArg ChapterB.baumann (map_subgroupOf_eq_of_le le_sup_right))
    have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs.1
    rw [Subgroup.map_sup, hbmap, source_join_residual D] at hm
    exact hm
  · exact Or.inr hf

/-- The original nonnormal A₅ case has no remaining module-equality or
minimal-parabolic premise before the marked symmetric-five branch. -/
theorem source_a5_baumann_normalizer_or_five_action_unconditional
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∨
      SourceFiveAction D :=
  source_local_baumann_normalizer_or_five_action D (source_a5_minimal_parabolic D e hn)

end CFSG.Quasithin.Chapter10
