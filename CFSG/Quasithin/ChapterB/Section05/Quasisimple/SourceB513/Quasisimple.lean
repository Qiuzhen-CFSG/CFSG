module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.IrreducibleCatalogue
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.Split
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SymplecticSource
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Descent
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.LinearThreeSource
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.AlternatingSource
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.OuterSymmetric
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SL2G2Source
/-!
# The quasisimple dual numerical branch of B.5.13

Apply the full corrected B.5.1 conclusion to the literal dual action. Split
moved modules use the complete irreducible catalogue or the three reducible
model bounds. The nonsplit list uses the proved natural-cover estimates,
and clause (4b) handles the complementary outer symmetric action.

The source wrapper takes the original B.5.3 FF hypothesis and derives the
needed offender from the nontrivial quasisimple generalized Fitting subgroup.
No model, field-size, supplement, dimension or offender bound remains an
additional premise. The B.5.1 conclusion is supplied by its existing source
producer at the final assembly.

Source: Aschbacher–Smith B.5.13, printed pp.110–112.
-/

public section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
theorem quadraticRatio_le_two_of_quasisimple_conclusion (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hq : IsQuasisimple (generalizedFitting G)) (hff : IsFFModule ρ.dual) :
    quadraticRatio ρ ≤ 2 := by
  have hqL : IsQuasisimple L := c.fitting_eq.symm ▸ hq
  let : Group.IsPerfect L := hqL.toIsPerfect
  let : IsSimpleGroup (L ⧸ center L) := hqL.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  by_cases hcL : IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L)
  · by_cases hcG : IsCompl c.sectionData.space.toSubmodule ρ.dual.invariants
    · cases c.clause_one with
      | irreducible hi hf hir hcase hext =>
        exact quadraticRatio_le_two_of_dual_fixed_supplement ρ c.sectionData.space hcG.sup_eq_top
          (irreducible_moved_bound c.sectionData hi hcL hff hcase)
      | doubleThree F hL e ho hr => exact doubleThree_dual_bound ρ c.sectionData hff F hL e
      | naturalDual d hd hL hn => exact naturalDual_dual_bound ρ c.sectionData hff (by omega) hL hn
      | repeatedNatural d r hd hr hb hL hn =>
        exact repeatedNatural_dual_bound ρ c.sectionData hff (by omega) hL hn
    · exact quadraticRatio_le_two_of_outer_symmetric_source c hq hcL hcG hff
  · cases (c.clause_two hcL).2 with
    | linearTwo F hn => exact quadraticRatio_le_two_of_linearTwo_source ρ c hcL F hn
    | symplectic F hn => exact quadraticRatio_le_two_of_symplectic_source c hq hcL F hn.some hff
    | g2 F hn => exact quadraticRatio_le_two_of_g2_source ρ c hcL F hn
    | alternatingSix hn => exact quadraticRatio_le_two_of_alternating_source c hcL (Or.inl rfl) hn hff
    | alternatingEight hn => exact quadraticRatio_le_two_of_alternating_source c hcL (Or.inr rfl) hn hff
    | derivedG2 hn => exact quadraticRatio_le_two_of_derivedG2_source ρ c hcL hn
    | linearThree hn => exact quadraticRatio_le_two_of_binary_linear_three_source c hq hcL hn hff

/-- The original dual FF hypothesis gives the numerical quasisimple B.5.13 branch. -/
theorem quadraticRatio_le_two_of_quasisimple_source {K : GroupClass} (ρ : Representation (ZMod 2) G V)
    (h : SourceInduction.FFHypothesis K ρ.dual)
    (hq : IsQuasisimple (generalizedFitting G))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual (generalizedFitting G)) :
    quadraticRatio ρ ≤ 2 := by
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) := hq.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  let : Nontrivial G := (generalizedFitting G).subtype_injective.nontrivial
  exact quadraticRatio_le_two_of_quasisimple_conclusion c hq (h.isFFModule ρ.dual)

end CFSG.Quasithin.ChapterB.SourceB513
