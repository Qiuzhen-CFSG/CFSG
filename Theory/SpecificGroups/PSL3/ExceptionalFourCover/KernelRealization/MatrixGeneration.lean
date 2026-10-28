module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.MatrixWords

/-!
# Surjectivity onto the actual matrix group

The checked words give a coordinate cycle and the two elementary root generators
x₀₁(1), x₀₁(z). Root addition, conjugation by the cycle and commutators give
all elementary matrices, hence SL₃(F₄). Projection and the proved field
isomorphism give the surjection onto the actual `Matrix.PSL3Four.PSL`.

The elementary-generation argument follows the existing
`Held/.../TwoA/ProjectiveComparison/Generators.lean`; its matrix witnesses
are replaced by the literal coordinates of this construction. The underlying
ATLAS elementary-generation API retains its license and attribution in
`Theory/AtlasPort/ExceptionalIsomorphisms/Elementary.lean`.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel
open Matrix.SpecialLinearGroup

private theorem field_cases : ∀ c : F, c = 0 ∨ c = 1 ∨ c = z ∨ c = z + 1 := by
  decide +kernel

private theorem cycle_root01 : ∀ c : F,
    cycle * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c * cycle⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c := by
  decide +kernel

private theorem cycle_root12 : ∀ c : F,
    cycle * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c * cycle⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c := by
  decide +kernel

/-- The two explicit matrix lifts generate the full special linear group. -/
theorem matrix_pair_generates : Subgroup.closure ({matrixX, matrixY} : Set SL) = ⊤ := by
  let K := Subgroup.closure ({matrixX, matrixY} : Set SL)
  have hX : matrixX ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hY : matrixY ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hcycle : cycle ∈ K := cycle_mem K hX hY
  have h01 (c : F) : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ K := by
    rcases field_cases c with rfl | rfl | rfl | rfl
    · simpa only [transvection_coeff_zero] using K.one_mem
    · exact rootOne_mem K hX hY
    · exact rootZ_mem K hX hY
    · rw [transvection_add]
      exact K.mul_mem (rootZ_mem K hX hY) (rootOne_mem K hX hY)
  have h12 (c : F) : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ K := by
    rw [← cycle_root01]
    exact K.mul_mem (K.mul_mem hcycle (h01 c)) (K.inv_mem hcycle)
  have h20 (c : F) : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ K := by
    rw [← cycle_root12]
    exact K.mul_mem (K.mul_mem hcycle (h12 c)) (K.inv_mem hcycle)
  have h02 (c : F) : Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h01 c) (h12 1))
    simpa only [Atlas.elementary_commutator (i := (0 : Fin 3)) (j := 2) (k := 1)
      (by decide) (by decide) (by decide) c 1, mul_one]
      using h
  have h10 (c : F) : Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h12 c) (h20 1))
    simpa only [Atlas.elementary_commutator (i := (1 : Fin 3)) (j := 0) (k := 2)
      (by decide) (by decide) (by decide) c 1, mul_one]
      using h
  have h21 (c : F) : Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ K := by
    have h := K.commutator_le_self (Subgroup.commutator_mem_commutator (h20 c) (h01 1))
    simpa only [Atlas.elementary_commutator (i := (2 : Fin 3)) (j := 1) (k := 0)
      (by decide) (by decide) (by decide) c 1, mul_one]
      using h
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ K) _ (fun _ _ => K.mul_mem) g
  intro i j hij c
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | exact h01 c | exact h02 c |
      exact h10 c | exact h12 c | exact h20 c | exact h21 c


/-- The third coordinate already covers the full special linear group. -/
theorem matrixProjection_surjective : Function.Surjective matrixProjection := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← matrix_pair_generates, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact ⟨generatorX, rfl⟩
  · obtain rfl := Set.mem_singleton_iff.mp hg
    exact ⟨generatorY, rfl⟩

/-- Surjectivity to the canonical matrix PSL group, with no recognition premise. -/
theorem projection_surjective : Function.Surjective projection :=
  (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv).surjective.comp
    ((QuotientGroup.mk'_surjective _).comp matrixProjection_surjective)

end Matrix.PSL3.ExceptionalFourCover.KernelModel
