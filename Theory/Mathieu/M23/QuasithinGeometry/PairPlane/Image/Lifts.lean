module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Lifting the field-plane generators into M23

The certified transvections fix the deleted pair pointwise, and the certified
Frobenius permutation swaps it. Their projective actions agree with the matrix
and field actions in the adjusted coordinates. Elementary generation then puts
the whole represented PSL subgroup in the pointwise-pair image.

Source: Aschbacher, *Sporadic Groups*, §18. Elementary generation uses the
existing attributed ATLAS port `ExceptionalIsomorphisms.Elementary`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage
open PairPlaneCoordinates Configuration Projectivization
open scoped Pointwise

private theorem mem_M23_of_reindex (g : Equiv.Perm (Fin 23))
    (f : Fin 253 → Fin 253) (hblock : ∀ i, g • m23BlockAt i = m23BlockAt (f i)) :
    g ∈ M23 := by
  have hf : Function.Injective f := by
    intro i j h
    apply m23BlockAt_injective
    apply (MulAction.injective g : Function.Injective (fun B : Finset (Fin 23) => g • B))
    change g • m23BlockAt i = g • m23BlockAt j
    rw [hblock, hblock, h]
  rw [mem_M23_iff]
  have h := congrArg (fun s : Finset (Finset (Fin 23)) => (s : Set (Finset (Fin 23))))
    (m23Blocks_smul_of_reindex g f (Finite.surjective_of_injective hf) hblock)
  simpa only [Finset.coe_smul_finset] using h

/-- Each elementary matrix's ambient permutation is a genuine M23 element. -/
theorem generatorPerm_mem (t : Fin 24) : generatorPerm t ∈ M23 :=
  mem_M23_of_reindex _ (generatorBlock t) fun i =>
    m23Perm_smul_blockAt_of_bits _ _ _ (generator_block_bits t i)

/-- Each elementary matrix lifts to the actual pair stabilizer. -/
noncomputable def generatorLift (t : Fin 24) : pairStabilizer :=
  ⟨⟨generatorPerm t, generatorPerm_mem t⟩, by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro z hz
    change generatorPoint t z ∈ x.val
    have hz' : z = 11 ∨ z = 17 := by simpa [x, label] using hz
    rcases hz' with rfl | rfl
    · rw [(generatorPoint_pair t).1]
      decide +kernel
    · rw [(generatorPoint_pair t).2]
      decide +kernel⟩

theorem generatorLift_pointwise (t : Fin 24) : generatorLift t ∈ pointwisePairStabilizer := by
  rw [mem_pointwisePairStabilizer]
  exact generatorPoint_pair t

@[simp] theorem generatorLift_labeledPoint (t : Fin 24) (i : Fin 21) :
    complementAction x.val (generatorLift t) (labeledPoint i) =
      labeledPoint (generatorRow t i) :=
  Subtype.ext (generatorPoint_labels t i)

/-- The determinant-one matrix corresponding to a certified generator. -/
noncomputable def generatorMatrix (t : Fin 24) : Matrix.PSL3Four.SL :=
  Matrix.SpecialLinearGroup.transvection (generator_ne t) (fieldEquiv (generatorCoeff t))

private theorem generator_field_vector (t : Fin 24) (i : Fin 21) :
    fieldEquiv (generatorScale t i) • fieldVector (pointRow (generatorRow t i)) =
      generatorMatrix t • fieldVector (pointRow i) := by
  funext k
  have h := congrArg fieldEquiv (congrFun (generator_vector t i) k)
  simpa [fieldVector, Pi.smul_apply, smul_eq_mul, generatorMatrix,
    Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.single_apply, apply_ite fieldEquiv] using h

/-- Both projective components of the lifted generator agree with its matrix action. -/
theorem generatorLift_collineation (t : Fin 24) :
    pairCollineation adjustedCoordinates (generatorLift t) =
      Matrix.PSL3Four.pslCollineation (generatorMatrix t : Matrix.PSL3Four.PSL) := by
  classical
  apply Collineation.ext_points
  intro p
  obtain ⟨q, rfl⟩ := adjustedCoordinates.pointEquiv.surjective p
  obtain ⟨i, rfl⟩ := pointLabelEquiv.surjective q
  change Collineation.pointHom PG PG _ (adjustedCoordinates.pointEquiv (labeledPoint i)) = _
  rw [pairCollineation_point, pairPointAction_apply, Equiv.symm_apply_apply,
    generatorLift_labeledPoint, adjusted_point_labeledPoint,
    Matrix.PSL3Four.pslCollineation_mk, specialLinearCollineation_point]
  change _ = generatorMatrix t • adjustedCoordinates.pointEquiv (labeledPoint i)
  rw [adjusted_point_labeledPoint]
  change projectivePoint (pointRow (generatorRow t i)) =
    generatorMatrix t • projectivePoint (pointRow i)
  rw [projectivePoint, projectivePoint, smul_mk]
  symm
  exact (mk_eq_mk_iff' _ _ _ _ _).mpr ⟨fieldEquiv (generatorScale t i), generator_field_vector t i⟩

/-- Every represented PSL element occurs already in the pointwise-pair image. -/
theorem psl_range_le_pointwise_image : Matrix.PSL3Four.pslCollineation.range ≤
    pointwisePairStabilizer.map (pairCollineation adjustedCoordinates) := by
  rintro c ⟨A, rfl⟩
  induction A using QuotientGroup.induction_on with | H A =>
  apply Atlas.sl_elementary_induction
    (fun A => Matrix.PSL3Four.pslCollineation (A : Matrix.PSL3Four.PSL) ∈
      pointwisePairStabilizer.map (pairCollineation adjustedCoordinates)) ?_ ?_ A
  · intro i j hij c
    obtain ⟨t, ht1, ht2, htc⟩ := generators_complete i j hij (fieldEquiv.symm c)
    have hc : fieldEquiv (generatorCoeff t) = c := by rw [htc, fieldEquiv.apply_symm_apply]
    have hmat : generatorMatrix t = Matrix.SpecialLinearGroup.transvection hij c := by
      unfold generatorMatrix
      subst i j
      rw [hc]
    exact ⟨generatorLift t, generatorLift_pointwise t, by rw [generatorLift_collineation, hmat]⟩
  · intro A B hA hB
    change Matrix.PSL3Four.pslCollineation ((A : Matrix.PSL3Four.PSL) * (B : Matrix.PSL3Four.PSL)) ∈ _
    rw [map_mul]
    exact Subgroup.mul_mem _ hA hB

/-- The coordinate field involution is induced by an actual M23 permutation. -/
theorem frobeniusPerm_mem : frobeniusPerm ∈ M23 :=
  mem_M23_of_reindex _ frobeniusBlock fun i =>
    m23Perm_smul_blockAt_of_bits _ _ _ (frobenius_block_bits i)

noncomputable def frobeniusLift : pairStabilizer :=
  ⟨⟨frobeniusPerm, frobeniusPerm_mem⟩, by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro z hz
    change frobeniusPoint z ∈ x.val
    have hz' : z = 11 ∨ z = 17 := by simpa [x, label] using hz
    rcases hz' with rfl | rfl <;> decide +kernel⟩

@[simp] theorem frobeniusLift_labeledPoint (i : Fin 21) :
    complementAction x.val frobeniusLift (labeledPoint i) = labeledPoint (frobeniusRow i) :=
  Subtype.ext (frobeniusPoint_labels i)

/-- The lifted involution acts as pure Frobenius after the diagonal adjustment. -/
theorem frobeniusLift_collineation :
    pairCollineation adjustedCoordinates frobeniusLift = Matrix.PSL3Four.frobeniusCollineation := by
  classical
  apply Collineation.ext_points
  intro p
  obtain ⟨q, rfl⟩ := adjustedCoordinates.pointEquiv.surjective p
  obtain ⟨i, rfl⟩ := pointLabelEquiv.surjective q
  change Collineation.pointHom PG PG _ (adjustedCoordinates.pointEquiv (labeledPoint i)) = _
  rw [pairCollineation_point, pairPointAction_apply, Equiv.symm_apply_apply,
    frobeniusLift_labeledPoint, adjusted_point_labeledPoint,
    Matrix.PSL3Four.frobeniusCollineation_point]
  change _ = Matrix.PSL3Four.projectiveFrobenius
    (adjustedCoordinates.pointEquiv (labeledPoint i))
  rw [adjusted_point_labeledPoint]
  rw [projectivePoint, projectivePoint, Matrix.PSL3Four.projectiveFrobenius_mk]
  congr 1
  funext k
  simp only [fieldVector, Function.comp_apply, Matrix.PSL3Four.fieldFrobenius_apply,
    frobenius_vector, map_pow]

end Sporadic.Mathieu.M23Geometry.PairPlaneImage
