module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.Definitions
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.WordEvaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.FixedVector

/-!
# Explicit witnesses for the trace-plane overgroup

The local word fixes the two marked plane vectors. Nine packed row products
certify the second vector's motion; the first uses the existing max1 fixed
vector proof. The source generator b moves the plane, proved at four chosen
coordinates. These checks establish an actual proper ambient stabilizer.
Moving the eight-subgroup itself remains a separate kernel-word calculation.

Source: ATLAS J4G1-f2r112B0 and J4G1-max1W1, as documented in the imported
matrix and local-word modules. Packed row arithmetic is checked by Lean.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup
open Janko4 Janko4.Cardinality Janko4.Cardinality.KernelCount Janko4.GeneratorCertificates
attribute [local irreducible] modelGroup matrixA matrixB

private def pv (n : ℕ) : CosetVector := fun j => bit n j.val
private theorem packed_row (n : ℕ) (r : Vector ℕ 112) :
    Matrix.vecMul (pv n) (decodeRows r) = pv (packedRow n r) := by
  funext j
  symm
  change bit (packedRow n r) j.val = _
  rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  change (∑ k : Fin 112, bit (if n.testBit k.val then r.get k else 0) j.val) =
    ∑ k : Fin 112, pv n k * decodeRows r k j
  apply Finset.sum_congr rfl
  intro k _
  simp only [pv, decodeRows, bit]
  cases n.testBit k.val <;> simp

private theorem step0 :
    packedRow 3683754961113342797877254413953002 xRows =
      860073714874574343315764596236170 := by decide +kernel

private theorem step1 :
    packedRow 860073714874574343315764596236170 yRows =
      4299490724284208070429531734745506 := by decide +kernel

private theorem step2 :
    packedRow 4299490724284208070429531734745506 yRows =
      3846647052992008348864444328149333 := by decide +kernel

private theorem step3 :
    packedRow 3846647052992008348864444328149333 xRows =
      4711463753742272343788532989151552 := by decide +kernel

private theorem step4 :
    packedRow 4711463753742272343788532989151552 yRows =
      3615747200856897888845929057748554 := by decide +kernel

private theorem step5 :
    packedRow 3615747200856897888845929057748554 xRows =
      4899345336097761926129410404438820 := by decide +kernel

private theorem step6 :
    packedRow 4899345336097761926129410404438820 yRows =
      2074159667442218326485929940722838 := by decide +kernel

private theorem step7 :
    packedRow 2074159667442218326485929940722838 yRows =
      1665442961625711392227901766689286 := by decide +kernel

private theorem step8 :
    packedRow 1665442961625711392227901766689286 xRows =
      1665442961625711392227901766689286 := by decide +kernel

private theorem second_transported :
    vectorRight firstPureSecondVector firstPureTransportWord =
      pv 1665442961625711392227901766689286 := by
  have hx : toMatrix (localX matrixA_mul_self matrixB_pow_four : Model) = decodeRows xRows :=
    Relations.representation_x _ _
  have hy : toMatrix (localY matrixA_mul_self matrixB_pow_four : Model) = decodeRows yRows :=
    Relations.representation_y _ _
  change vectorRight (pv 3683754961113342797877254413953002) firstPureTransportWord = _
  simp only [firstPureTransportWord, vectorRight_mul]
  simp only [vectorRight, hx, hy,
    packed_row, step0, step1, step2, step3, step4, step5, step6, step7]

/-- The explicit local word fixes the second plane vector. -/
theorem firstPureStrictWitness_fixes_second :
    vectorRight firstPureSecondVector firstPureStrictWitness = firstPureSecondVector := by
  have hx : toMatrix (localX matrixA_mul_self matrixB_pow_four : Model) = decodeRows xRows :=
    Relations.representation_x _ _
  have hfixed : vectorRight (pv 1665442961625711392227901766689286)
      (localX matrixA_mul_self matrixB_pow_four : Model) =
        pv 1665442961625711392227901766689286 := by
    change Matrix.vecMul _ _ = _
    rw [hx, packed_row, step8]
  rw [firstPureStrictWitness, vectorRight_mul, vectorRight_mul,
    second_transported, hfixed, ← second_transported,
    ← vectorRight_mul, mul_inv_cancel, vectorRight_one]

/-- The explicit local word fixes the first plane vector using its max1 membership. -/
theorem firstPureStrictWitness_fixes_base :
    vectorRight cosetBaseVector firstPureStrictWitness = cosetBaseVector := by
  let M := max1Subgroup matrixA_mul_self matrixB_pow_four
  have hw : firstPureTransportWord ∈ M := by
    unfold firstPureTransportWord
    exact M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem
      (M.mul_mem (localX _ _).property (localY _ _).property)
      (localY _ _).property) (localX _ _).property) (localY _ _).property)
      (localX _ _).property) (localY _ _).property) (localY _ _).property
  exact max1Subgroup_le_cosetVectorStabilizer _ _
    (M.mul_mem (M.mul_mem hw (localX _ _).property) (M.inv_mem hw))

/-- The strictness witness fixes every vector of the proposed trace plane. -/
theorem firstPureStrictWitness_fixes_plane (v : CosetVector) (hv : v ∈ firstPurePlane) :
    vectorRight v firstPureStrictWitness = v := by
  obtain ⟨i, rfl⟩ := hv
  fin_cases i
  · change vectorRight 0 _ = 0
    exact Matrix.zero_vecMul _
  · exact firstPureStrictWitness_fixes_base
  · exact firstPureStrictWitness_fixes_second
  · change Matrix.vecMul (cosetBaseVector + firstPureSecondVector) _ = _
    rw [Matrix.add_vecMul]
    exact congrArg₂ (· + ·) firstPureStrictWitness_fixes_base firstPureStrictWitness_fixes_second

/-- The marked word belongs to the full ambient plane stabilizer. -/
theorem firstPureStrictWitness_mem_planeStabilizer :
    firstPureStrictWitness ∈ firstPurePlaneStabilizer := by
  intro v
  constructor
  · intro hv
    have h := congrArg (fun w => vectorRight w firstPureStrictWitness⁻¹)
      (firstPureStrictWitness_fixes_plane _ hv)
    simp only [← vectorRight_mul, mul_assoc, mul_inv_cancel, mul_one, vectorRight_one] at h
    rwa [h] at hv
  · intro hv
    rw [firstPureStrictWitness_fixes_plane v hv]
    exact hv

/-- Four coordinate inequalities exclude all four proposed plane vectors. -/
private theorem source_b_moves_base_outside :
    ∀ i : Fin 4, Matrix.vecMul cosetBaseVector matrixB (![1, 0, 4, 0] i) ≠
      firstPurePlaneVector i (![1, 0, 4, 0] i) := by decide +kernel

/-- The second ATLAS generator does not stabilize the plane setwise. -/
theorem source_b_not_mem_firstPurePlaneStabilizer :
    Janko4.b ∉ firstPurePlaneStabilizer := by
  intro hb
  have hv : vectorRight cosetBaseVector Janko4.b ∈ firstPurePlane :=
    (hb cosetBaseVector).mpr ⟨1, rfl⟩
  obtain ⟨i, hi⟩ := hv
  apply source_b_moves_base_outside i
  simpa only [vectorRight, Janko4.toMatrix_b] using
    congrFun hi.symm (![1, 0, 4, 0] i)

/-- The geometric overgroup is proper independently of the trace-image calculation. -/
theorem firstPurePlaneStabilizer_ne_top : firstPurePlaneStabilizer ≠ ⊤ := by
  intro h
  exact source_b_not_mem_firstPurePlaneStabilizer (h.symm ▸ mem_top _)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
