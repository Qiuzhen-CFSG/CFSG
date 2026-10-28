module

/-
Adapted from Atlas/Comparisons/Exceptional/PSL2NineGenerators.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.NineCoordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Tactic.FinCases
set_option warningAsError false

@[expose] public section

/-!
# Generators over the nine-element field

Translations by one and omega generate every upper transvection. Conjugating
by inversion gives the lower transvections, so special-linear transvection
induction proves generation, which then descends to the central quotient.
-/


namespace Atlas.Comparisons.Exceptional.Nine
open Matrix
open scoped MatrixGroups

def upperOne : SL(2,F) :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) 1

def upperOmega : SL(2,F) :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) omega

def inversionMatrix : SL(2,F) := ⟨!![0,-1;1,0], by decide⟩

theorem upper_coordinates (c : F) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c =
      upperOne ^ c.re.val * upperOmega ^ c.im.val := by
  have h : ∀ c : F, Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) c =
      upperOne ^ c.re.val * upperOmega ^ c.im.val := by decide
  exact h c

theorem lower_coordinates (c : F) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c =
      inversionMatrix * (upperOne ^ (-c).re.val * upperOmega ^ (-c).im.val) *
        inversionMatrix⁻¹ := by
  have h : ∀ c : F, Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) c =
      inversionMatrix * (upperOne ^ (-c).re.val * upperOmega ^ (-c).im.val) *
        inversionMatrix⁻¹ := by decide
  exact h c

theorem sl_generated :
    Subgroup.closure ({upperOne,upperOmega,inversionMatrix} : Set SL(2,F)) = ⊤ := by
  let H := Subgroup.closure ({upperOne,upperOmega,inversionMatrix} : Set SL(2,F))
  have h1 : upperOne ∈ H := Subgroup.subset_closure (by simp)
  have hw : upperOmega ∈ H := Subgroup.subset_closure (by simp)
  have ht : inversionMatrix ∈ H := Subgroup.subset_closure (by simp)
  apply top_unique
  intro g _
  apply Matrix.SL2.transvection_induction (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij c
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · rw [upper_coordinates]; exact H.mul_mem (H.pow_mem h1 _) (H.pow_mem hw _)
  · rw [lower_coordinates]
    exact H.mul_mem (H.mul_mem ht (H.mul_mem (H.pow_mem h1 _) (H.pow_mem hw _)))
      (H.inv_mem ht)
  · exact (hij rfl).elim

def generators : Set PSL(2,F) :=
  {(upperOne : PSL(2,F)), (upperOmega : PSL(2,F)), (inversionMatrix : PSL(2,F))}

theorem psl_generated : Subgroup.closure generators = ⊤ := by
  let π := QuotientGroup.mk' (Subgroup.center SL(2,F))
  have he : generators = π '' ({upperOne,upperOmega,inversionMatrix} : Set SL(2,F)) := by
    ext g; simp [generators,π, eq_comm]
  rw [he,← MonoidHom.map_closure,sl_generated]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
end Atlas.Comparisons.Exceptional.Nine
