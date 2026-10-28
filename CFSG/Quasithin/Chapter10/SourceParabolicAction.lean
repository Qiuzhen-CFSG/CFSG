module
public import CFSG.Quasithin.Chapter10.SourceParabolicControl
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteOrbitSpan

/-!
# The original E.2.3 action in the Chapter 10 normalizer argument

The local orbit supplied by the Fundamental Setup is reduced in L₀T.
Under the original minimal-parabolic conclusion, the completed E.2.3
classification gives either its Baumann Sylow conclusion or a literal
marked symmetric-five action. The former now gives N_G(Baum(T))≤M by
the common-normal theorem. If J(T) centralizes the module, the earlier
kernel uniqueness gives the same bound directly.

The remaining alternatives retain the exact original local quotient,
module and Sylow subgroup, including the paired action's prescribed
exchanging element. Only the original 10.1.2(6) minimal-parabolic premise
and V=V_T in its first two rows are supplied by the preceding module
analysis. This is the source reduction in 10.2.1, not its longer A₅
elimination or the final normalization theorem.
Source: Aschbacher–Smith, 10.1.2 and 10.2.1, printed pp.742–743,
using E.2.3, printed pp.216–217.
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

private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The literal local module is reduced, with the earlier A/C input discharged. -/
theorem source_parabolic_module_reduced :
    IsPReduced 2 (D.moduleSubgroup.subgroupOf (localJoin T L)) :=
  D.module_reduced (source_uniqueness D)

/-- The exact marked symmetric-five alternatives in E.2.3, on the local
module constructed by the original Fundamental Setup. -/
@[expose] def SourceFiveAction : Prop :=
    let U := D.moduleSubgroup.subgroupOf (localJoin T L)
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set (localJoin T L))
    SymmetricFiveSingleSource U (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) ∨
      SymmetricFivePairSource (T.subtype le_sup_right) U (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)

/-- The complete E.2.3 linear branch in source 10.2.1; the only exceptional
outputs are the original marked symmetric-five actions on the same module. -/
theorem source_baumann_normalizer_or_five_action
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤)
    (hfull : D.fullModule = D.moduleSubgroup) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∨
      SourceFiveAction D := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)
  · exact Or.inl (source_baumann_normalizer_le_of_centralizes D (hfull.symm ▸ hJ))
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
  rcases source_linear_conclusions_or_symmetric_five
    (D.local_internal_module (source_uniqueness D)).sqtk S hP U hU hmove with hs | hf
  · apply Or.inl
    have hu : Order.HasUniqueMaximalOver (T : Subgroup G) H := by
      have hh := hasUniqueMaximalOver_map_subtype
        ((ChapterB.isMinimalParabolicOver_iff S ⊤).mp hP).1
      have he : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
        map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
      exact he ▸ hh
    apply source_baumann_normalizer_le_of_orbit_sylow D hu
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

end CFSG.Quasithin.Chapter10
