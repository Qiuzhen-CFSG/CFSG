module

/-
Adapted from Atlas/Comparisons/Exceptional/Order168.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.PSL2SevenAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.SingerEightAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.FiniteGeneratorActionComparison
set_option warningAsError false

public section


/-! The two actual matrix groups have the same faithful eight-point action.
The source generators are the projective translation and inversion; the target
acts by conjugation on its eight cyclic Singer subgroups. -/
noncomputable section
namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups

private theorem generator_images : ∀ g ∈ Seven.generators,
    Seven.permutation g ∈ SingerEight.action.range := by
  intro g hg
  rcases hg with rfl | hg
  · refine ⟨SingerEight.U, ?_⟩
    rw [Seven.permutation_upper]
    apply Equiv.ext
    intro i
    rw [SingerEight.action_U]
    rfl
  · have he : g = (Seven.inversionMatrix : PSL(2,Seven.F)) := Set.mem_singleton_iff.mp hg
    subst g
    refine ⟨SingerEight.T, ?_⟩
    rw [Seven.permutation_inversion]
    apply Equiv.ext
    intro i
    rw [SingerEight.action_T]
    rfl

/-- Identification through the common faithful action on eight points. -/
def psl2SevenEquivSl3Two : PSL(2,ZMod 7) ≃* SL(3,ZMod 2) :=
  Atlas.GroupTheory.equivOfGeneratorActions Seven.permutation SingerEight.action
    Seven.permutation_injective SingerEight.action_injective
    (psl2Seven_card.trans sl3Two_card.symm) Seven.generators Seven.psl_generated generator_images

/-- The exceptional order-168 comparison, for the actual projective matrix groups. -/
def psl2SevenEquivPsl3Two : PSL(2,ZMod 7) ≃* PSL(3,ZMod 2) :=
  psl2SevenEquivSl3Two.trans sl3TwoEquivPsl3Two

theorem psl2SevenEquivSl3Two_action (g : PSL(2,ZMod 7)) :
    SingerEight.action (psl2SevenEquivSl3Two g) = Seven.permutation g :=
  Atlas.GroupTheory.equivOfGeneratorActions_coherence _ _ _ _ _ _ _ _ g

end Atlas.Comparisons.Exceptional
