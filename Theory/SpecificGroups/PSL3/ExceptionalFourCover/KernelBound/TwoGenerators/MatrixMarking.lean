module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.Presentation
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.MatrixMarking.Generators
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# The four-relator presentation surjects onto matrix PSL₃(4)

The explicit matrices in `MatrixMarking.Words` satisfy the three power
relators in SL and the mixed relator modulo the scalar center. Their elementary
root words generate SL. Transport through the proved field isomorphism and
the actual projective quotient therefore gives a surjective homomorphism
from the literal `Presentation` to `Matrix.PSL3Four.PSL`.

This is the matrix-comparison input to
`two_sylow_rank_le_two_of_presentation_surjective`; no presentation order,
multiplier structure, or group-recognition hypothesis is used here.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11,
https://staff.itee.uq.edu.au/havas/2004chrr.pdf.
-/

@[expose] public section

namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation
namespace MatrixMarking

/-- Field transport followed by the actual quotient by the scalar center. -/
noncomputable def projection : SL →* PSL3Four.PSL :=
  (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv).toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center SL))

theorem projection_surjective : Function.Surjective projection :=
  (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv).surjective.comp
    (QuotientGroup.mk'_surjective _)

theorem projection_scalarZ : projection scalarZ = 1 := by
  have h : QuotientGroup.mk' (Subgroup.center SL) scalarZ = 1 :=
    (QuotientGroup.eq_one_iff scalarZ).mpr scalarZ_mem_center
  simp only [projection, MonoidHom.comp_apply, h, map_one]

/-- The ordered matrix marking of the two printed generators. -/
noncomputable def generators : Fin 2 → PSL3Four.PSL := ![projection A, projection B]

theorem relators_hold : ∀ r ∈ relators, FreeGroup.lift generators r = 1 := by
  have ha : FreeGroup.lift generators a = projection A := by simp [a, generators]
  have hb : FreeGroup.lift generators b = projection B := by simp [b, generators]
  intro r hr
  simp only [relators, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [map_pow, ha, ← map_pow, A_fifth, map_one]
  · rw [map_pow, hb, ← map_pow, B_fifth, map_one]
  · rw [map_pow, map_mul, ha, hb, ← map_mul, ← map_pow, AB_cube, map_one]
  · simp only [mixed, map_mul, map_pow, map_inv, ha, hb]
    simpa only [map_mul, map_pow, map_inv, projection_scalarZ] using
      congrArg projection mixed_scalar

end MatrixMarking

/-- The four-relator presentation mapped to the actual matrix PSL₃(4). -/
noncomputable def matrixMap : Presentation →* PSL3Four.PSL :=
  PresentedGroup.toGroup MatrixMarking.relators_hold

@[simp] theorem matrixMap_of_zero :
    matrixMap (PresentedGroup.of 0) = MatrixMarking.projection MatrixMarking.A := by
  exact PresentedGroup.toGroup.of MatrixMarking.relators_hold

@[simp] theorem matrixMap_of_one :
    matrixMap (PresentedGroup.of 1) = MatrixMarking.projection MatrixMarking.B := by
  exact PresentedGroup.toGroup.of MatrixMarking.relators_hold

/-- The explicit map is onto, by the checked elementary root words in its lifts. -/
theorem matrixMap_surjective : Function.Surjective matrixMap := by
  let K := matrixMap.range.comap MatrixMarking.projection
  have hA : MatrixMarking.A ∈ K := ⟨PresentedGroup.of 0, matrixMap_of_zero⟩
  have hB : MatrixMarking.B ∈ K := ⟨PresentedGroup.of 1, matrixMap_of_one⟩
  have hK : K = ⊤ := by
    apply top_unique
    rw [← MatrixMarking.pair_generates, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hA
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact hB
  intro g
  obtain ⟨x, rfl⟩ := MatrixMarking.projection_surjective g
  have hx : x ∈ K := by rw [hK]; trivial
  exact hx

/-- The matrix comparison required by the presentation-based kernel rank bound. -/
theorem exists_surjective_matrix_map :
    ∃ f : Presentation →* PSL3Four.PSL, Function.Surjective f :=
  ⟨matrixMap, matrixMap_surjective⟩

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation
