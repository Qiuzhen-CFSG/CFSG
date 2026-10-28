module

public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootRecognition
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Geometry
import Mathlib.Tactic.FinCases

/-!
# Generating the subfield symplectic group from four opposite central axes

The long-root Weyl word interchanges the first hyperbolic pair and carries
the two short central roots to the mixed roots. The short-root Weyl word
carries the first long-root pair to the second pair. Thus the two central
root families and their actual opposition conjugates generate all eight
root groups. Coefficient inclusion retains the original subfield embedding.

This closes the full-center source case of Aschbacher--Smith E.2.7,
printed pp.219--221. Extracting full subfield axes from a smaller V remains
a separate assertion; it is not a hypothesis hidden in this generation proof.
-/

public section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [CharP F 2]

private def n₀ : Sp F := rootElement 0 1 * rootElement 1 1 * rootElement 0 1
private def n₄ : Sp F := rootElement 4 1 * rootElement 5 1 * rootElement 4 1

private theorem n₀_matrix : (n₀ (F := F)).val =
    fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1] := by
  change rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.add_self_eq_zero]

private theorem n₄_matrix : (n₄ (F := F)).val =
    fromBlocks 0 !![0,1;1,0] !![0,1;1,0] 0 := by
  change rootMatrix 4 1 * rootMatrix 5 1 * rootMatrix 4 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.add_self_eq_zero]

private theorem n₀_short (t : F) :
    n₀ * rootElement 4 t * n₀ = rootElement 7 t ∧
    n₀ * rootElement 5 t * n₀ = rootElement 6 t := by
  constructor
  · apply Subtype.ext
    change (n₀ (F := F)).val * rootMatrix 4 t * (n₀ (F := F)).val = rootMatrix 7 t
    rw [n₀_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq]
  · apply Subtype.ext
    change (n₀ (F := F)).val * rootMatrix 5 t * (n₀ (F := F)).val = rootMatrix 6 t
    rw [n₀_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq]

private theorem n₄_long (t : F) :
    n₄ * rootElement 0 t * n₄ = rootElement 3 t ∧
    n₄ * rootElement 1 t * n₄ = rootElement 2 t := by
  constructor
  · apply Subtype.ext
    change (n₄ (F := F)).val * rootMatrix 0 t * (n₄ (F := F)).val = rootMatrix 3 t
    rw [n₄_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.single, Matrix.fromBlocks]
  · apply Subtype.ext
    change (n₄ (F := F)).val * rootMatrix 1 t * (n₄ (F := F)).val = rootMatrix 2 t
    rw [n₄_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.single, Matrix.fromBlocks]

/-- Four opposite central-root families generate the actual symplectic matrix group. -/
theorem eq_top_of_four_axes (H : Subgroup (Sp F))
    (h₀ : ∀ t : F, rootElement 0 t ∈ H)
    (h₁ : ∀ t : F, rootElement 1 t ∈ H)
    (h₄ : ∀ t : F, rootElement 4 t ∈ H)
    (h₅ : ∀ t : F, rootElement 5 t ∈ H) : H = ⊤ := by
  have hn₀ : n₀ (F := F) ∈ H := H.mul_mem (H.mul_mem (h₀ 1) (h₁ 1)) (h₀ 1)
  have hn₄ : n₄ (F := F) ∈ H := H.mul_mem (H.mul_mem (h₄ 1) (h₅ 1)) (h₄ 1)
  have h₂ (t : F) : rootElement 2 t ∈ H := by
    rw [← (n₄_long t).2]
    exact H.mul_mem (H.mul_mem hn₄ (h₁ t)) hn₄
  have h₃ (t : F) : rootElement 3 t ∈ H := by
    rw [← (n₄_long t).1]
    exact H.mul_mem (H.mul_mem hn₄ (h₀ t)) hn₄
  have h₆ (t : F) : rootElement 6 t ∈ H := by
    rw [← (n₀_short t).2]
    exact H.mul_mem (H.mul_mem hn₀ (h₅ t)) hn₀
  have h₇ (t : F) : rootElement 7 t ∈ H := by
    rw [← (n₀_short t).1]
    exact H.mul_mem (H.mul_mem hn₀ (h₄ t)) hn₀
  apply eq_top_of_rootElement_mem
  intro r t
  fin_cases r
  · exact h₀ t
  · exact h₁ t
  · exact h₂ t
  · exact h₃ t
  · exact h₄ t
  · exact h₅ t
  · exact h₆ t
  · exact h₇ t

/-- The fixed opposition matrix carries the two central axes to their negative roots. -/
theorem opposition_central_axes (t : F) :
    opposition * rootElement 0 t * opposition⁻¹ = rootElement 1 t ∧
    opposition * rootElement 4 t * opposition⁻¹ = rootElement 5 t := by
  rw [opposition_inv]
  constructor
  · apply Subtype.ext
    change fromBlocks 0 1 1 0 * rootMatrix 0 t * fromBlocks 0 1 1 0 = rootMatrix 1 t
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.single, Matrix.fromBlocks]
  · apply Subtype.ext
    change fromBlocks 0 1 1 0 * rootMatrix 4 t * fromBlocks 0 1 1 0 = rootMatrix 5 t
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.single, Matrix.fromBlocks]

/-- The actual opposite pair is all of Sp₄ when V contains both central-root axes. -/
theorem oppositePair_eq_top_of_axes (V : Subgroup (Sp F))
    (h₀ : ∀ t : F, rootElement 0 t ∈ V)
    (h₄ : ∀ t : F, rootElement 4 t ∈ V) : oppositePair V = ⊤ := by
  apply eq_top_of_four_axes
  · intro t
    exact (show V ≤ oppositePair V from le_sup_left) (h₀ t)
  · intro t
    rw [← (opposition_central_axes t).1]
    exact (show V.map (MulAut.conj (opposition (F := F))).toMonoidHom ≤ oppositePair V from le_sup_right) (mem_map_of_mem (MulAut.conj opposition).toMonoidHom (h₀ t))
  · intro t
    exact (show V ≤ oppositePair V from le_sup_left) (h₄ t)
  · intro t
    rw [← (opposition_central_axes t).2]
    exact (show V.map (MulAut.conj (opposition (F := F))).toMonoidHom ≤ oppositePair V from le_sup_right) (mem_map_of_mem (MulAut.conj opposition).toMonoidHom (h₄ t))


/-- Coefficient inclusion preserves the fixed, literal opposition matrix. -/
theorem coefficientInclusion_opposition (K : Subfield F) :
    coefficientInclusion K (opposition (F := K)) = opposition (F := F) := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [coefficientInclusion_apply, opposition, Matrix.fromBlocks]

/-- The two-conjugate construction commutes with the original coefficient inclusion. -/
theorem oppositePair_map_coefficient (K : Subfield F) (V : Subgroup (Sp K)) :
    oppositePair (V.map (coefficientInclusion K)) =
      (oppositePair V).map (coefficientInclusion K) := by
  have he : (MulAut.conj (opposition (F := F))).toMonoidHom.comp
      (coefficientInclusion K) = (coefficientInclusion K).comp
        (MulAut.conj (opposition (F := K))).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change opposition * coefficientInclusion K x * opposition⁻¹ =
      coefficientInclusion K (opposition * x * opposition⁻¹)
    rw [map_mul, map_mul, map_inv, coefficientInclusion_opposition]
  simp only [oppositePair, Subgroup.map_sup, Subgroup.map_map, he]

/-- The full central-root parameter plane and its opposite generate Sp₄. -/
theorem oppositePair_parameter_range :
    oppositePair (CentralRootGeometry.parameter (F := F)).range = ⊤ := by
  apply oppositePair_eq_top_of_axes
  · intro t
    refine ⟨(Multiplicative.ofAdd t, 1), ?_⟩
    simp [CentralRootGeometry.parameter_apply, RootSubgroup.element_zero]
  · intro t
    refine ⟨(1, Multiplicative.ofAdd t), ?_⟩
    simp [CentralRootGeometry.parameter_apply, RootSubgroup.element_zero]

/-- In particular, the actual opposite pair of the full center over K equals
precisely the original embedded subfield symplectic group. -/
theorem oppositePair_coefficient_parameter_range (K : Subfield F) :
    oppositePair ((CentralRootGeometry.parameter (F := K)).range.map
      (coefficientInclusion K)) = (coefficientInclusion K).range := by
  rw [oppositePair_map_coefficient, oppositePair_parameter_range,
    ← MonoidHom.range_eq_map]

/-- Four coefficient axes, with opposition in the original ambient group,
force containment of the entire original coefficient-subfield copy. -/
theorem coefficientSubfield_le_of_four_axes (K : Subfield F) (H : Subgroup (Sp F))
    (h₀ : ∀ t : K, coefficientInclusion K (rootElement 0 t) ∈ H)
    (h₄ : ∀ t : K, coefficientInclusion K (rootElement 4 t) ∈ H)
    (h₁ : ∀ t : K, opposition * coefficientInclusion K (rootElement 0 t) *
      opposition⁻¹ ∈ H)
    (h₅ : ∀ t : K, opposition * coefficientInclusion K (rootElement 4 t) *
      opposition⁻¹ ∈ H) : (coefficientInclusion K).range ≤ H := by
  have hJ : H.comap (coefficientInclusion K) = ⊤ := by
    apply eq_top_of_four_axes
    · exact h₀
    · intro t
      have he := congrArg (coefficientInclusion K)
        (opposition_central_axes (F := K) t).1
      rw [map_mul, map_mul, map_inv, coefficientInclusion_opposition] at he
      change coefficientInclusion K (rootElement 1 t) ∈ H
      rw [← he]
      exact h₁ t
    · exact h₄
    · intro t
      have he := congrArg (coefficientInclusion K)
        (opposition_central_axes (F := K) t).2
      rw [map_mul, map_mul, map_inv, coefficientInclusion_opposition] at he
      change coefficientInclusion K (rootElement 5 t) ∈ H
      rw [← he]
      exact h₅ t
  rintro x ⟨y, rfl⟩
  have hy : y ∈ H.comap (coefficientInclusion K) := by rw [hJ]; trivial
  exact hy

/-- The literal source subgroup V need only contain the two coefficient axes;
its own opposition-generated subgroup then contains the subfield copy. -/
theorem coefficientSubfield_le_oppositePair (K : Subfield F) (V : Subgroup (Sp F))
    (h₀ : ∀ t : K, coefficientInclusion K (rootElement 0 t) ∈ V)
    (h₄ : ∀ t : K, coefficientInclusion K (rootElement 4 t) ∈ V) :
    (coefficientInclusion K).range ≤ oppositePair V := by
  apply coefficientSubfield_le_of_four_axes K
  · intro t
    exact (show V ≤ oppositePair V from le_sup_left) (h₀ t)
  · intro t
    exact (show V ≤ oppositePair V from le_sup_left) (h₄ t)
  · intro t
    exact (show V.map (MulAut.conj (opposition (F := F))).toMonoidHom ≤
      oppositePair V from le_sup_right)
        (mem_map_of_mem (MulAut.conj opposition).toMonoidHom (h₀ t))
  · intro t
    exact (show V.map (MulAut.conj (opposition (F := F))).toMonoidHom ≤
      oppositePair V from le_sup_right)
        (mem_map_of_mem (MulAut.conj opposition).toMonoidHom (h₄ t))

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
