module
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceEquality

/-!
# The actual solvable two-chief-factor qrc branch

Under Hypothesis 3.1.5 and uniqueness of the maximal two-local overgroup,
the common-normal alternative is excluded by the existing source theorem.
The actual qrc configuration therefore has exactly two noncentral factors
in the multiple-factor, ratio-two branch, using the proved D.1.3 actor
and equality family. This is the numerical branch in 3.1.9(1); exclusion
of the distinct dual-FF and unique-factor branches remains separate.
Source: Aschbacher–Smith 3.1.9(1), printed pp.576–577.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.solvable_noncentral_count_two
    (h : QrcHypotheses T M M₀ H V)
    (hu : ∀ L : Subgroup G, IsMaximalTwoLocal L → M₀ ≤ L → L = M)
    (hne : V ≠ ⊥) (hV : V ≤ ChapterD.twoCoreIn H) (hs : Group.IsSolvable H)
    (hq : letI := h.module_elementary
      quadraticRatio (ChapterD.UniqueFactor.imageRepresentation M₀ V h.module_normalized) = 2)
    (s : SeriesOn ((ChapterD.conjugateSpan H V).subgroupOf H)) (hc : 1 < s.noncentralCount) :
    s.noncentralCount = 2 := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  have hnf := ChapterD.UniqueFactor.source_notFF_of_ratio_two d hq
  let := ChapterD.UniqueFactor.source_elementary_span_of_notFF d hV hnf
  let U := (ChapterD.conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((ChapterD.UniqueFactor.span_le_right_core d hV).trans (ChapterD.UniqueFactor.twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T :=
    map_subgroupOf_eq_of_le h.right_mem.1.1.2
  obtain ⟨A,hA,hAR,hquad⟩ := ChapterD.UniqueFactor.source_quadratic_max_actor d hne hV hnf S hS
  have hnc : ¬ A ≤ centralizer (U : Set H) := by
    intro ha
    exact hAR ((le_inf hA.1 ha).trans
      (ChapterD.UniqueFactor.source_span_centralizer_sylow_le_core d hne hV hnf S hS))
  exact (ChapterD.UniqueFactor.source_solvable_multiple_equalities d hne hV hs hq
    S hS s hc A hA hquad hnc).1
end CFSG.Quasithin.Chapter3
