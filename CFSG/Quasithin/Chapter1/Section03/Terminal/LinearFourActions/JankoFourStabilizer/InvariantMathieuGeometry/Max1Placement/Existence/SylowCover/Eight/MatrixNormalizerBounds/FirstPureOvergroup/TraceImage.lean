module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.KernelWords
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Injectivity.Packed
public import Mathlib.Algebra.CharP.Two
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.TraceImage.Arithmetic
/-!
# The trace image of the first pure kernel eight

Coordinate injectivity gives a bijection from the eight literal masks to the
actual subgroup, so reindexing its trace counts every element exactly once.
The generators 198, 1688 and 821 factor this sum into three displacement
operators. The packed certificate evaluates that product: all rows lie in the
specified binary plane, and rows 1 and 3 give its two spanning vectors.
Consequently the full image is exactly the four literal vectors.

This discharges the trace-image premise of
`FirstPureOvergroup.row_zero_of_mask_trace_and_word_equalities`. The separate
three PC-word comparisons are retained by the assembly owner. The companion
application here transports the image to the actual first pure row `U 0`.

Source context: Aschbacher–Smith A.3.12, `refs/quasithin.pdf`, printed pp.47–48.
This finite certificate uses the unchanged ATLAS representation and kernel
coordinates attributed in `Model.Data`, `KernelCount.Tables`, and
`KernelOrbits.Coordinates`. Discovery provenance is recorded in
`FirstPureOvergroup/source/README.md`; the discovery output is not assumed.
-/

public section
open Janko4 Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.QuotientCount.Image Janko4.Simplicity.Max1Fusion.KernelOrbits
open Janko4.GeneratorCertificates
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed

private theorem mask_injective : Function.Injective (fun i : Fin 8 => kernelMask (firstPureMask i)) := by
  intro i j h
  have he : maskValue matrixA_mul_self matrixB_pow_four (firstPureMask i) =
      maskValue matrixA_mul_self matrixB_pow_four (firstPureMask j) := Subtype.ext (Subtype.ext h)
  have hb := coordinates_injective matrixA_mul_self matrixB_pow_four he
  have hi : Function.Injective (fun i : Fin 8 => fun k : Fin 11 => (firstPureMask i).testBit k.val) := by decide +kernel
  exact hi hb

private noncomputable def maskEquiv : Fin 8 ≃ firstPureMaskEight :=
  Equiv.ofBijective (fun i => ⟨kernelMask (firstPureMask i), i, rfl⟩)
    ⟨fun i j h => mask_injective (congrArg (fun u : firstPureMaskEight => (u : Model)) h), by
      rintro ⟨g, i, rfl⟩
      exact ⟨i, rfl⟩⟩

private theorem trace_sum (v : CosetVector) :
    firstPureMaskTrace v = ∑ i : Fin 8, vectorRight v (kernelMask (firstPureMask i)) := by
  classical
  let := Fintype.ofFinite firstPureMaskEight
  exact (maskEquiv.sum_comp (fun u : firstPureMaskEight => vectorRight v (u : Model))).symm

private theorem km_xor (m n : ℕ) :
    kernelMask (Nat.xor m n) = kernelMask m * kernelMask n := by
  simp only [kernelMask, maskValue_xor, map_mul]
private theorem km_zero : kernelMask 0 = 1 := by
  simp only [kernelMask, maskValue_zero, map_one]

attribute [local irreducible] kernelMask decodeRows basisRows cosetBaseVector firstPureSecondVector

private theorem trace_factor (v : CosetVector) :
    firstPureMaskTrace v =
      let w := v + vectorRight v (kernelMask 198)
      let u := w + vectorRight w (kernelMask 1688)
      u + vectorRight u (kernelMask 821) := by
  rw [trace_sum]
  dsimp only
  simp only [vectorRight, Matrix.add_vecMul, Matrix.vecMul_vecMul, ← map_mul]
  have h1 : kernelMask 198 * kernelMask 1688 = kernelMask 1630 := (km_xor 198 1688).symm
  have h2 : kernelMask 198 * kernelMask 821 = kernelMask 1011 := (km_xor 198 821).symm
  have h3 : kernelMask 1688 * kernelMask 821 = kernelMask 1453 := (km_xor 1688 821).symm
  have h4 : kernelMask 1630 * kernelMask 821 = kernelMask 1387 := (km_xor 1630 821).symm
  simp only [h1, h2, h3, h4]
  simp only [Fin.sum_univ_succ, firstPureMask, Matrix.cons_val_zero, Matrix.cons_val_succ,
    km_zero, map_one, Matrix.vecMul_one]
  abel

private theorem matrix_mask (m : ℕ) : toMatrix (kernelMask m) = matrixProduct (fun i => m.testBit i.val) := by
  unfold kernelMask
  change representation matrixA_mul_self matrixB_pow_four (maskValue matrixA_mul_self matrixB_pow_four m) = _
  change representation matrixA_mul_self matrixB_pow_four (coordinates matrixA_mul_self matrixB_pow_four _) = _
  rw [coordinates_val]
  exact representation_binaryProduct _ _ (representation_basis _ _) _

private theorem expand_198 {G : Type*} [Monoid G] (e : Fin 11 → G) :
    binaryProduct e (fun j => (198 : ℕ).testBit j.val) = e 1 * e 2 * e 6 * e 7 := by
  have h : (fun j : Fin 11 => (198 : ℕ).testBit j.val) =
      ![false, true, true, false, false, false, true, true, false, false, false] := by decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ, mul_assoc]

private theorem matrix_198 : toMatrix (kernelMask 198) = decodeRows (basisRows 1) * decodeRows (basisRows 2) * decodeRows (basisRows 6) * decodeRows (basisRows 7) :=
  (matrix_mask 198).trans (expand_198 (fun i => decodeRows (basisRows i)))

private theorem expand_1688 {G : Type*} [Monoid G] (e : Fin 11 → G) :
    binaryProduct e (fun j => (1688 : ℕ).testBit j.val) = e 3 * e 4 * e 7 * e 9 * e 10 := by
  have h : (fun j : Fin 11 => (1688 : ℕ).testBit j.val) =
      ![false, false, false, true, true, false, false, true, false, true, true] := by decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ, mul_assoc]

private theorem matrix_1688 : toMatrix (kernelMask 1688) = decodeRows (basisRows 3) * decodeRows (basisRows 4) * decodeRows (basisRows 7) * decodeRows (basisRows 9) * decodeRows (basisRows 10) :=
  (matrix_mask 1688).trans (expand_1688 (fun i => decodeRows (basisRows i)))

private theorem expand_821 {G : Type*} [Monoid G] (e : Fin 11 → G) :
    binaryProduct e (fun j => (821 : ℕ).testBit j.val) = e 0 * e 2 * e 4 * e 5 * e 8 * e 9 := by
  have h : (fun j : Fin 11 => (821 : ℕ).testBit j.val) =
      ![true, false, true, false, true, true, false, false, true, true, false] := by decide +kernel
  rw [h]
  simp [binaryProduct, List.ofFn_succ, mul_assoc]

private theorem matrix_821 : toMatrix (kernelMask 821) = decodeRows (basisRows 0) * decodeRows (basisRows 2) * decodeRows (basisRows 4) * decodeRows (basisRows 5) * decodeRows (basisRows 8) * decodeRows (basisRows 9) :=
  (matrix_mask 821).trans (expand_821 (fun i => decodeRows (basisRows i)))

private theorem plane_add {v w : CosetVector} (hv : v ∈ firstPurePlane)
    (hw : w ∈ firstPurePlane) : v + w ∈ firstPurePlane := by
  rcases hv with ⟨i, rfl⟩
  rcases hw with ⟨j, rfl⟩
  refine ⟨(![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] i j), ?_⟩
  fin_cases i <;> fin_cases j <;> funext k <;>
    simp [firstPurePlaneVector, Pi.add_apply, add_comm, add_left_comm,
      CharTwo.add_self_eq_zero, CharTwo.add_cancel_left]

private def planeModule : Submodule (ZMod 2) CosetVector where
  carrier := firstPurePlane
  zero_mem' := ⟨0, rfl⟩
  add_mem' := plane_add
  smul_mem' := by
    intro c v hv
    have hc := (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide +kernel) c
    rcases hc with rfl | rfl
    · simpa using (show (0 : CosetVector) ∈ firstPurePlane from ⟨0, rfl⟩)
    · simpa using hv

private theorem image_of_rows (T : BinaryMatrix)
    (hrows : ∀ i, T i ∈ firstPurePlane)
    (hf : T 1 = cosetBaseVector) (hv : T 3 = firstPureSecondVector) :
    Set.range (fun v => Matrix.vecMul v T) = firstPurePlane := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    change Matrix.vecMul v T ∈ firstPurePlane
    rw [Matrix.vecMul_eq_sum]
    exact planeModule.sum_mem (fun i _ => planeModule.smul_mem (v i) (hrows i))
  · rintro _ ⟨i, rfl⟩
    have hbase : Matrix.vecMul (Pi.single 1 1) T = cosetBaseVector := by
      simpa only [Matrix.single_one_vecMul, Matrix.row] using hf
    have hsecond : Matrix.vecMul (Pi.single 3 1) T = firstPureSecondVector := by
      simpa only [Matrix.single_one_vecMul, Matrix.row] using hv
    fin_cases i
    · exact ⟨0, Matrix.zero_vecMul _⟩
    · exact ⟨Pi.single 1 1, hbase⟩
    · exact ⟨Pi.single 3 1, hsecond⟩
    · exact ⟨Pi.single 1 1 + Pi.single 3 1, by
        change Matrix.vecMul (Pi.single 1 1 + Pi.single 3 1) T = _
        rw [Matrix.add_vecMul, hbase, hsecond]
        rfl⟩

private theorem planePacked_eq (i : Fin 4) :
    (fun j : Fin 112 => bit (FirstPureTraceArithmetic.planePacked i) j.val) =
      firstPurePlaneVector i := by
  fin_cases i
  · funext j
    simp [FirstPureTraceArithmetic.planePacked, firstPurePlaneVector, bit]
  · unfold FirstPureTraceArithmetic.planePacked firstPurePlaneVector cosetBaseVector
    rfl
  · unfold FirstPureTraceArithmetic.planePacked firstPurePlaneVector firstPureSecondVector
    rfl
  · funext j
    change bit (1383886125678978288045195946262397 ^^^
      3683754961113342797877254413953002) j.val =
        cosetBaseVector j + firstPureSecondVector j
    unfold cosetBaseVector firstPureSecondVector
    exact bit_xor 1383886125678978288045195946262397
      3683754961113342797877254413953002 j.val

private theorem trace_matrix (v : CosetVector) :
    firstPureMaskTrace v = Matrix.vecMul v
      (fun i => firstPurePlaneVector (FirstPureTraceArithmetic.rowIndex i) : BinaryMatrix) := by
  have step (w : CosetVector) (g : Model) : w + vectorRight w g =
      Matrix.vecMul w (1 + toMatrix g) := by
    simp only [Matrix.vecMul_add, Matrix.vecMul_one, vectorRight]
  rw [trace_factor]
  dsimp only
  simp only [step, Matrix.vecMul_vecMul, matrix_198, matrix_1688, matrix_821]
  rw [FirstPureTraceArithmetic.factor_rows]
  congr 1
  funext i
  exact planePacked_eq _

/-- The complete trace of the actual eight-element kernel subgroup has exactly
    the four literal plane vectors as its image. No PC-word comparison is needed. -/
theorem firstPureMaskTrace_range : Set.range firstPureMaskTrace = firstPurePlane := by
  have ht : firstPureMaskTrace = fun v => Matrix.vecMul v
      (fun i => firstPurePlaneVector (FirstPureTraceArithmetic.rowIndex i) : BinaryMatrix) :=
    funext trace_matrix
  rw [ht]
  exact image_of_rows _ (fun i => ⟨FirstPureTraceArithmetic.rowIndex i, rfl⟩) rfl rfl

/-- Application to the original first pure row: only the independent three
    PC-word comparisons remain, and the complete subgroup trace is transported. -/
theorem firstPureTrace_range_of_word_equalities
    (h18 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 18 : Model) =
      kernelMask 1011)
    (h19 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 19 : Model) =
      kernelMask 1387)
    (h20 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 20 : Model) =
      kernelMask 198) :
    Set.range firstPureTrace = firstPurePlane := by
  rw [firstPureTrace_eq_maskTrace_of_word_equalities h18 h19 h20]
  exact firstPureMaskTrace_range

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
