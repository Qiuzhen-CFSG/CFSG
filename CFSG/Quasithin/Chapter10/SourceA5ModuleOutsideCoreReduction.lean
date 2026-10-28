module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalOutsideReduction
/-!
# The original local A5 module outside-core numerical reduction

The literal local module and local join satisfy the source qrc hypotheses.
The no-TI E.2 reduction now discharges every original outside-core row except
odd PSL3 and nonbinary Sp4. This consumer uses the same H, module, quotient
action and two-core as the original module-selection argument; it introduces
neither a TI condition nor normalization of the module by H ∩ M.

Source: Aschbacher--Smith 3.1.6 and 3.2.5--6, printed pp.573--581, as used
in the A5 module selection in 10.1. The displayed exceptional models remain
mathematical obligations for the unconditional local bound.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original module's outside-core case has only the two source model
obligations remaining after the no-TI witness construction. -/
theorem source_localModule_outsideCore_cubic_bound_or_exceptional_model
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hout : ¬ D.moduleSubgroup ≤ H.pCoreIn 2) :
    SourceLocalModuleCubicBound D ∨
      (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).HasExceptionalOutsideCoreModel := by
  rcases (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).outsideCore_cubicRatio_le_two_or_exceptional_model
    D.simpleQTKE
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2 hout with hq | hm
  · exact Or.inl (source_localModule_cubic_bound_of_image D hq)
  · exact Or.inr hm

/-- Refine the original source alternatives without choosing a new module or H. -/
theorem source_module_cubic_bounds_or_model_or_dualFF
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    ∃ H, ∃ hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      (SourceLocalModuleCubicBound D ∨
        (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).HasExceptionalOutsideCoreModel ∨
        SourceLocalModuleDualFF D) ∧
      (SourceFullModuleCubicBound D ∨ SourceFullModuleDualFF D) := by
  obtain ⟨H,hH,hl,hf⟩ := source_module_cubic_bounds_or_source_branches D hout
  refine ⟨H,hH,?_,hf⟩
  rcases hl with hq | ho | hd
  · exact Or.inl hq
  · rcases source_localModule_outsideCore_cubic_bound_or_exceptional_model D hH ho with hq | hm
    · exact Or.inl hq
    · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr hd)

end CFSG.Quasithin.Chapter10
