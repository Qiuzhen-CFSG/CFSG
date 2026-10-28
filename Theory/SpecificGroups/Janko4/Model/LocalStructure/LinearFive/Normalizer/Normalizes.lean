module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Evaluation

/-!
# Two literal ambient normalizer elements

The checked left-conjugation equations show directly that the aligned ATLAS
words normalize the constructed F. Finiteness supplies the reverse inclusion.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.NativeNormalizer
open Cardinality KernelCount
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY

def actionMasks : Fin 2 → Fin 10 → ℕ :=
  ![![247,868,24,803,807,779,897,39,502,358],
    ![746,722,12,83,868,396,492,600,116,603]]

def element : Fin 2 → Model := ![n0,n1]

theorem element_conjugates (i : Fin 2) (j : Fin 10) :
    element i * (generators j : Model) * (element i)⁻¹ = fValue (actionMasks i j) := by
  fin_cases i <;> fin_cases j
  · exact conjugate_0_0
  · exact conjugate_0_1
  · exact conjugate_0_2
  · exact conjugate_0_3
  · exact conjugate_0_4
  · exact conjugate_0_5
  · exact conjugate_0_6
  · exact conjugate_0_7
  · exact conjugate_0_8
  · exact conjugate_0_9
  · exact conjugate_1_0
  · exact conjugate_1_1
  · exact conjugate_1_2
  · exact conjugate_1_3
  · exact conjugate_1_4
  · exact conjugate_1_5
  · exact conjugate_1_6
  · exact conjugate_1_7
  · exact conjugate_1_8
  · exact conjugate_1_9

private theorem F_closure : F = Subgroup.closure (Set.range (fun i => (generators i : Model))) := by
  rw [F, localF, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem element_mem_normalizer (i : Fin 2) : element i ∈ Subgroup.normalizer (F : Set Model) := by
  apply Subgroup.mem_normalizer_fintype
  have h : F ≤ F.comap (MulAut.conj (element i)).toMonoidHom := by
    nth_rw 1 [F_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨j,rfl⟩
    change element i * (generators j : Model) * (element i)⁻¹ ∈ F
    rw [element_conjugates]
    exact fValue_mem _
  intro x hx
  exact h hx

def normalizerElement (i : Fin 2) : Subgroup.normalizer (F : Set Model) :=
  ⟨element i, element_mem_normalizer i⟩

end Janko4.LocalStructure.LinearFive.NativeNormalizer
