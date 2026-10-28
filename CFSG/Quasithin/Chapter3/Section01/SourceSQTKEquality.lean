module
public import CFSG.Quasithin.Chapter3.Section01.ReducedModuleSylow
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SQTKEquality
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.MinimalActor

/-!
# The original SQTK two-chief-factor equalities with a minimal actor

The actual qrc source excludes zero and one noncentral chief factors. Its
ratio-two equality theorem then forces exactly two factors without assuming
that the right-hand local group is solvable. A single maximum elementary
actor is chosen quadratic with minimum nontrivial image modulo the right
core. The full rank and centralizer identities hold for that same actor in
every chief series and on every literal conjugate of the original module.

The module is the one in QrcHypotheses; it may therefore be the moved
four-space chosen in notation15.1.4. The source inside-core, nondual-FF and
ratio-two premises remain explicit until the earlier classification and
inside-core producers supply them.

Source: Aschbacher--Smith3.1.9(1--3) and15.1.12(1--2), pp.576--577,1089--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_noncentral_count_two
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) : s.noncentralCount = 2 := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  have hn := noncentralCount_ne_zero d hne hV s
  have hnotone : s.noncentralCount ≠ 1 := by
    intro hc
    have hh : HasUniqueNoncentralChiefFactor H V := ⟨s,hc⟩
    rcases source_dualFF_or_coreClosure_centralizes d hV hh with hd | hc
    · exact hdual hd
    · exact h.not_uniqueFactor_coreClosure_centralizes hG hM hu hJ hV hh hc
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  obtain ⟨A,hA,hAR,hquad⟩ := source_quadratic_max_actor d hne hV hnf S hS
  have hnc : ¬ A ≤ centralizer (U : Set H) := by
    intro ha
    exact hAR ((le_inf hA.1 ha).trans
      (source_span_centralizer_sylow_le_core d hne hV hnf S hS))
  exact (source_sqtk_multiple_equalities d hne hV
    (sqtk_of_mem_H hG h.right_mem.1.1.1) hq S hS s (by omega) A hA hquad hnc).1


theorem QrcHypotheses.sqtk_minimal_actor_equalities
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    let S := T.subtype h.right_mem.1.1.2
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H ∧
      IsQuadratic (normalRepresentation U) A ∧
      (∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
        ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
      ∀ s : SeriesOn U,
        s.noncentralCount = 2 ∧
        2 * Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (normalRepresentation U) A ∧
        fixedCodim (normalRepresentation U) A =
          2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ pCore 2 H)) ∧
        U ⊓ centralizer (A : Set H) = U ⊓ centralizer (A ⊓ pCore 2 H : Set H) ∧
        (∀ i, ¬ s.Central i →
          Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (s.factorRepresentation i) A) ∧
        ∀ g : H,
          (fixedCodim (conjugateGenerator d (A ⊓ pCore 2 H) inf_le_right g).toRepresentation ⊤ : ℝ) =
            2 * (Nat.log 2 (subspaceKernel ((normalRepresentation U).comp (A ⊓ pCore 2 H).subtype)
              (conjugateGenerator d (A ⊓ pCore 2 H) inf_le_right g).toSubmodule ⊤).index : ℝ) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  dsimp only
  obtain ⟨A,hA,hAR,hquad,hmin⟩ := source_quadratic_minimal_max_actor d hne hV hnf S hS
  refine ⟨A,hA,hAR,hquad,hmin,?_⟩
  intro s
  have hc := h.sqtk_noncentral_count_two hG hM hu hJ hne hV hdual hq s
  have hnc : ¬ A ≤ centralizer (U : Set H) := by
    intro ha
    exact hAR ((le_inf hA.1 ha).trans
      (source_span_centralizer_sylow_le_core d hne hV hnf S hS))
  exact source_sqtk_multiple_equalities d hne hV
    (sqtk_of_mem_H hG h.right_mem.1.1.1) hq S hS s (by omega) A hA hquad hnc
end CFSG.Quasithin.Chapter3
