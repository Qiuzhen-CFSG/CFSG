module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalSymplecticExceptions
/-!
# The original local A5 action with only symplectic recognition remaining

The no-TI odd PSL3 bound applies to the literal local module and local join.
The source numerical alternatives therefore retain only the proper noncyclic
symplectic central-plane model, together with the separate dual-FF branch.
The original H and both module actions are retained.

Source: Aschbacher--Smith 3.1.6 and 3.2.5--6, printed pp.573--581,
as used in the A5 module selection in 10.1. The displayed symplectic
recognition case is still a mathematical obligation for the local bound.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original outside-core local module has only the symplectic
pair-recognition obligation after the no-TI source bounds. -/
theorem source_localModule_outsideCore_cubic_bound_or_symplectic_middle_model
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hout : ¬ D.moduleSubgroup ≤ H.pCoreIn 2) :
    SourceLocalModuleCubicBound D ∨
      (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).HasSymplecticMiddleOutsideCoreModel := by
  rcases (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).outsideCore_cubicRatio_le_two_or_symplectic_middle_model
    D.simpleQTKE
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).1
    (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.2 hout with hq | hm
  · exact Or.inl (source_localModule_cubic_bound_of_image D hq)
  · exact Or.inr hm

/-- The same selected H retains both literal module actions and the single
remaining outside-core recognition case. -/
theorem source_module_cubic_bounds_or_symplectic_model_or_dualFF
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    ∃ H, ∃ hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      (SourceLocalModuleCubicBound D ∨
        (D.qrcHypotheses (source_module_nonsolvable_uniqueness D) hH).HasSymplecticMiddleOutsideCoreModel ∨
        SourceLocalModuleDualFF D) ∧
      (SourceFullModuleCubicBound D ∨ SourceFullModuleDualFF D) := by
  obtain ⟨H,hH,hl,hf⟩ := source_module_cubic_bounds_or_source_branches D hout
  refine ⟨H,hH,?_,hf⟩
  rcases hl with hq | ho | hd
  · exact Or.inl hq
  · rcases source_localModule_outsideCore_cubic_bound_or_symplectic_middle_model D hH ho with hq | hm
    · exact Or.inl hq
    · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr hd)

end CFSG.Quasithin.Chapter10
