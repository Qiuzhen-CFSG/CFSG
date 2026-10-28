module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.MatrixData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent
/-!
# Restriction of the integral block group modulo two

The invariant rows from `MatrixData` extend from the generators to their
subgroup closure. Their right inverse proves uniqueness, hence restriction
is a homomorphism into SL₃(GF(4)). Scalar transport defines `matrixQuotient`
with the exact field used by the Leech block consumer. Its kernel consists
precisely of elements fixing those rows, and contains the scalar signs.

This module does not assert faithfulness of the restricted modular action
or exactness of the integral reduction kernel. Those are separate recognition
steps. The conventions and numerical source are John Bray's ATLAS
`6L34G1-Ar6aB0.M`, as recorded in `MatrixData`.
-/

public section
open Atlas.Algebra Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
private abbrev reduceAmbient := Matrix.GeneralLinearGroup.map (n := Fin 6) reductionScalars

private theorem restriction_mul {g h : GL (Fin 6) Eisenstein} {a b : SL(3,GoldenFour)}
    (ha : a.val * modularRows = modularRows * (reduceAmbient g).val)
    (hb : b.val * modularRows = modularRows * (reduceAmbient h).val) :
    (a * b).val * modularRows = modularRows * (reduceAmbient (g * h)).val := by
  change (a.val * b.val) * modularRows = _
  rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  rw [map_mul, GeneralLinearGroup.coe_mul]

private theorem restriction_inv {g : GL (Fin 6) Eisenstein} {a : SL(3,GoldenFour)}
    (ha : a.val * modularRows = modularRows * (reduceAmbient g).val) :
    a⁻¹.val * modularRows = modularRows * (reduceAmbient g⁻¹).val := by
  have hl : a⁻¹.val * a.val = (1 : Matrix _ _ GoldenFour) :=
    congrArg (fun x : SL(3,GoldenFour) => x.val) (inv_mul_cancel a)
  have hr : (reduceAmbient g).val * (reduceAmbient g⁻¹).val = 1 := by
    change (reduceAmbient g * reduceAmbient g⁻¹).val = 1
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have h := congrArg (fun m => a⁻¹.val * m * (reduceAmbient g⁻¹).val) ha
  rw [← Matrix.mul_assoc a⁻¹.val a.val modularRows, hl, Matrix.one_mul] at h
  simpa only [Matrix.mul_assoc, hr, Matrix.mul_one] using h.symm

private theorem exists_restriction (g : matrixGroup) :
    ∃ a : SL(3,GoldenFour), a.val * modularRows = modularRows * (reduction g).val := by
  obtain ⟨g, hg⟩ := g
  change ∃ a : SL(3,GoldenFour), a.val * modularRows = modularRows * (reduceAmbient g).val
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨threeA, threeA_rows⟩
    · exact ⟨threeB, threeB_rows⟩
  | one => exact ⟨1, by simp⟩
  | mul g h _ _ hg hh =>
    obtain ⟨a, ha⟩ := hg
    obtain ⟨b, hb⟩ := hh
    exact ⟨a * b, restriction_mul ha hb⟩
  | inv g _ hg =>
    obtain ⟨a, ha⟩ := hg
    exact ⟨a⁻¹, restriction_inv ha⟩

/-- Restriction to the displayed invariant row space over the retained GF(4). -/
noncomputable def goldenQuotient : matrixGroup →* SL(3,GoldenFour) where
  toFun g := (exists_restriction g).choose
  map_one' := by
    apply Subtype.ext
    apply modularRows_cancel
    change (exists_restriction 1).choose.val * modularRows = (1 : Matrix _ _ GoldenFour) * modularRows
    simpa only [map_one, GeneralLinearGroup.coe_one, Matrix.mul_one,
      Matrix.one_mul] using (exists_restriction 1).choose_spec
  map_mul' g h := by
    apply Subtype.ext
    apply modularRows_cancel
    exact (exists_restriction (g * h)).choose_spec.trans
      (restriction_mul (exists_restriction g).choose_spec
        (exists_restriction h).choose_spec).symm

theorem goldenQuotient_rows (g : matrixGroup) :
    (goldenQuotient g).val * modularRows = modularRows * (reduction g).val :=
  (exists_restriction g).choose_spec

@[expose] def matrixGeneratorA : matrixGroup := ⟨generatorA, Subgroup.subset_closure (by simp)⟩
@[expose] def matrixGeneratorB : matrixGroup := ⟨generatorB, Subgroup.subset_closure (by simp)⟩

@[simp] theorem goldenQuotient_generatorA : goldenQuotient matrixGeneratorA = threeA := by
  apply Subtype.ext
  exact modularRows_cancel ((goldenQuotient_rows _).trans threeA_rows.symm)
@[simp] theorem goldenQuotient_generatorB : goldenQuotient matrixGeneratorB = threeB := by
  apply Subtype.ext
  exact modularRows_cancel ((goldenQuotient_rows _).trans threeB_rows.symm)

/-- The actual integral matrix group acting on the three-space over `Embedding.F`. -/
@[expose] noncomputable def matrixQuotient : matrixGroup →* SL(3,F) :=
  (SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom).comp goldenQuotient

theorem goldenQuotient_eq_iff (g : matrixGroup) (a : SL(3,GoldenFour)) :
    goldenQuotient g = a ↔ a.val * modularRows = modularRows * (reduction g).val := by
  constructor
  · rintro rfl
    exact goldenQuotient_rows g
  · intro h
    apply Subtype.ext
    exact modularRows_cancel ((goldenQuotient_rows g).trans h.symm)

/-- The restricted matrix can be read directly from the three pivot columns. -/
theorem goldenQuotient_matrix (g : matrixGroup) :
    (goldenQuotient g).val = modularRows * (reduction g).val * modularSection := by
  have h := congrArg (fun m => m * modularSection) (goldenQuotient_rows g)
  simpa only [Matrix.mul_assoc, modularRows_section, Matrix.mul_one] using h

theorem threeGenerated_le_goldenQuotient_range :
    Subgroup.closure {threeA, threeB} ≤ goldenQuotient.range := by
  apply (Subgroup.closure_le _).mpr
  rintro _ (rfl | rfl)
  · exact ⟨matrixGeneratorA, goldenQuotient_generatorA⟩
  · exact ⟨matrixGeneratorB, goldenQuotient_generatorB⟩

theorem matrixQuotient_scalar_map (g : matrixGroup) :
    SpecialLinearGroup.map scalarFieldEquiv.toRingHom (matrixQuotient g) =
      goldenQuotient g := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact scalarFieldEquiv.apply_symm_apply _

theorem matrixQuotient_eq_one_iff (g : matrixGroup) :
    matrixQuotient g = 1 ↔ goldenQuotient g = 1 := by
  constructor
  · intro h
    rw [← matrixQuotient_scalar_map, h, map_one]
  · intro h
    change SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom (goldenQuotient g) = 1
    rw [h, map_one]

/-- The kernel test uses the literal six-dimensional reduction and row embedding. -/
theorem matrixQuotient_mem_ker_iff (g : matrixGroup) :
    g ∈ matrixQuotient.ker ↔ modularRows * (reduction g).val = modularRows := by
  rw [MonoidHom.mem_ker, matrixQuotient_eq_one_iff, goldenQuotient_eq_iff]
  change (1 : Matrix _ _ GoldenFour) * modularRows = _ ↔ _
  rw [Matrix.one_mul]
  exact eq_comm

theorem reduction_ker_le_matrixQuotient_ker : reduction.ker ≤ matrixQuotient.ker := by
  intro g hg
  rw [matrixQuotient_mem_ker_iff, MonoidHom.mem_ker.mp hg]
  exact Matrix.mul_one _

theorem matrixSigns_le_reduction_ker : matrixSigns ≤ reduction.ker := by
  intro g hg
  rw [mem_matrixSigns] at hg
  change GeneralLinearGroup.map reductionScalars g.val = 1
  rcases hg with h | h
  · rw [h, map_one]
  · rw [h]
    apply Units.ext
    change reductionScalars.mapMatrix (-1) = 1
    rw [map_neg, map_one]
    ext i j <;> simp [CharTwo.neg_eq]

theorem matrixSigns_le_matrixQuotient_ker : matrixSigns ≤ matrixQuotient.ker :=
  matrixSigns_le_reduction_ker.trans reduction_ker_le_matrixQuotient_ker

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
