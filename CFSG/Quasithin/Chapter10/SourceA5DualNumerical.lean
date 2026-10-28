module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter3.Section01.SourceDualNumerical
/-!
# Discharging the original A₅ module dual-FF alternatives

The complete B.5.13 theorem applies to the original local and full qrc
actions and their literal centralizer quotients. It removes both dual-FF
alternatives. The full module therefore has cubic ratio at most two;
the local module retains only the independent outside-core source branch.
The original outside-maximal guard is retained.

Source: Aschbacher--Smith B.5.13 and 3.1.6--8, the numerical inputs to the
module selection in 3.2.5--6 and the A₅ branch of Chapter 10.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_localModule_cubic_bound_of_dualFF {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hd : SourceLocalModuleDualFF D) : SourceLocalModuleCubicBound D :=
  source_localModule_cubic_bound_of_image D
    ((D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).cubicRatio_le_two_of_dualFF
      D.simpleQTKE (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hd)

theorem source_fullModule_cubic_bound_of_dualFF {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hd : SourceFullModuleDualFF D) : SourceFullModuleCubicBound D :=
  source_fullModule_cubic_bound_of_image D
    ((source_fullModule_qrcHypotheses D hH).cubicRatio_le_two_of_dualFF
      D.simpleQTKE (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1 hd)

theorem source_module_cubic_bounds_or_outside_core
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      (SourceLocalModuleCubicBound D ∨ ¬ D.moduleSubgroup ≤ H.pCoreIn 2) ∧
      SourceFullModuleCubicBound D := by
  obtain ⟨H,hH,hl,hf⟩ := source_module_cubic_bounds_or_source_branches D hout
  refine ⟨H,hH,?_,?_⟩
  · rcases hl with hl | ho | hd
    · exact Or.inl hl
    · exact Or.inr ho
    · exact Or.inl (source_localModule_cubic_bound_of_dualFF D hH hd)
  · exact hf.elim id (source_fullModule_cubic_bound_of_dualFF D hH)

theorem source_full_module_cubic_bound
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    SourceFullModuleCubicBound D := by
  obtain ⟨_,_,_,hf⟩ := source_module_cubic_bounds_or_outside_core D hout
  exact hf
end CFSG.Quasithin.Chapter10
