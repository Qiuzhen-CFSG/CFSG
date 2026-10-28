module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.PlaneWitness
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.KernelWords
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.TraceImage
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.WordComparison

/-!
# A trace-image route for the first pure Sylow eight

Conjugation by an ambient normalizer element permutes every element in the
subgroup trace. Consequently the entire ambient normalizer preserves its
image. Identifying that image with the specified plane reduces the requested
strict proper-overgroup alternative to two finite witness checks: one local
word preserves the plane but moves the subgroup, and the source generator
`b` moves the plane.

The imported leaves certify the trace image, the three literal PC-word
comparisons, the plane witness and its motion of the eight, and properness
of the plane stabilizer. The final theorem `row_zero` discharges all these
premises and proves the unconditional first-row normalizer alternative:
the full ambient normalizer lies strictly inside a proper plane stabilizer.
Source context: Aschbacher–Smith A.3.12, printed pp.47–48; the literal matrix
and word sources are recorded in `FirstPureOvergroup.Definitions`.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.Cardinality
attribute [local irreducible] modelGroup matrixA matrixB

/-- Reindexing the complete subgroup trace gives equivariance under its full
ambient normalizer. No involution class or containing local subgroup is assumed. -/
theorem firstPureTrace_normalizer (g : Model)
    (hg : g ∈ normalizer (U 0 : Set Model)) (v : CosetVector) :
    firstPureTrace (vectorRight v g) = vectorRight (firstPureTrace v) g := by
  classical
  let := Fintype.ofFinite (U 0)
  let e : U 0 ≃ U 0 :=
    { toFun := fun u => ⟨g * (u : Model) * g⁻¹,
        (mem_normalizer_iff.mp hg (u : Model)).mp u.property⟩
      invFun := fun u => ⟨g⁻¹ * (u : Model) * g,
        by simpa only [inv_inv] using
          (mem_normalizer_iff.mp ((normalizer (U 0 : Set Model)).inv_mem hg)
            (u : Model)).mp u.property⟩
      left_inv := by intro u; apply Subtype.ext; simp only [mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one]
      right_inv := by intro u; apply Subtype.ext; simp only [mul_assoc, mul_inv_cancel_left,
        mul_inv_cancel, mul_one] }
  have he (u : U 0) :
      vectorRight (vectorRight v g) (u : Model) =
        vectorRight (vectorRight v (e u : Model)) g := by
    simp only [← vectorRight_mul]
    congr 1
    change g * (u : Model) = (g * (u : Model) * g⁻¹) * g
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  change (∑ u : U 0, vectorRight (vectorRight v g) (u : Model)) =
    vectorRight (∑ u : U 0, vectorRight v (u : Model)) g
  simp_rw [he]
  rw [show (∑ u : U 0, vectorRight (vectorRight v (e u : Model)) g) =
    ∑ u : U 0, vectorRight (vectorRight v (u : Model)) g from
      e.sum_comp (fun u : U 0 => vectorRight (vectorRight v (u : Model)) g)]
  exact (Matrix.sum_vecMul _ _ _).symm

/-- Trace-image equality controls the full ambient normalizer. -/
theorem firstPure_normalizer_le_planeStabilizer
    (himage : Set.range firstPureTrace = firstPurePlane) :
    normalizer (U 0 : Set Model) ≤ firstPurePlaneStabilizer := by
  intro g hg v
  rw [← himage]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨vectorRight w g⁻¹, ?_⟩
    rw [firstPureTrace_normalizer g⁻¹ ((normalizer (U 0 : Set Model)).inv_mem hg),
      hw, ← vectorRight_mul, mul_inv_cancel, vectorRight_one]
  · rintro ⟨w, rfl⟩
    exact ⟨vectorRight w g, firstPureTrace_normalizer g hg w⟩

/-- The two concrete witnesses give the strict proper-overgroup alternative
once the finite trace-image identity has been certified. -/
theorem row_zero_of_trace_plane_certificates
    (himage : Set.range firstPureTrace = firstPurePlane)
    (hfix : firstPureStrictWitness ∈ firstPurePlaneStabilizer)
    (hmove : firstPureStrictWitness ∉ normalizer (U 0 : Set Model))
    (hproper : Janko4.b ∉ firstPurePlaneStabilizer) :
    EightNormalizerAlternative (U 0) := by
  right
  refine ⟨firstPurePlaneStabilizer,
    lt_of_le_not_ge (firstPure_normalizer_le_planeStabilizer himage)
      (fun h => hmove (h hfix)), ?_⟩
  intro htop
  exact hproper (htop.symm ▸ mem_top _)

/-- The geometric witness and properness are discharged by checked row arithmetic;
only the subgroup trace and the word's failure to normalize remain. -/
theorem row_zero_of_trace_image_and_moved_eight
    (himage : Set.range firstPureTrace = firstPurePlane)
    (hmove : firstPureStrictWitness ∉ normalizer (U 0 : Set Model)) :
    EightNormalizerAlternative (U 0) :=
  row_zero_of_trace_plane_certificates himage firstPureStrictWitness_mem_planeStabilizer
    hmove source_b_not_mem_firstPurePlaneStabilizer

/-- Only finite trace and PC-word certificates remain in the first pure-row route. -/
theorem row_zero_of_trace_image_and_word_equalities
    (himage : Set.range firstPureTrace = firstPurePlane)
    (h18 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 18 : Model) =
      kernelMask 1011)
    (h19 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 19 : Model) =
      kernelMask 1387)
    (h20 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 20 : Model) =
      kernelMask 198) :
    EightNormalizerAlternative (U 0) :=
  row_zero_of_trace_image_and_moved_eight himage
    (firstPureStrictWitness_not_normalizer_of_word_equalities h18 h19 h20)

/-- The trace calculation on eight explicit kernel words and the independent
PC-word comparisons supply the full first pure-row normalizer alternative. -/
theorem row_zero_of_mask_trace_and_word_equalities
    (himage : Set.range firstPureMaskTrace = firstPurePlane)
    (h18 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 18 : Model) =
      kernelMask 1011)
    (h19 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 19 : Model) =
      kernelMask 1387)
    (h20 : (Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator 20 : Model) =
      kernelMask 198) :
    EightNormalizerAlternative (U 0) := by
  apply row_zero_of_trace_image_and_word_equalities _ h18 h19 h20
  rw [firstPureTrace_eq_maskTrace_of_word_equalities h18 h19 h20]
  exact himage

/-- The full ambient normalizer of the first literal pure row lies strictly
inside the proper trace-plane stabilizer. All trace and word certificates
are discharged on the actual J₄ matrix carrier. -/
theorem row_zero : EightNormalizerAlternative (U 0) :=
  row_zero_of_mask_trace_and_word_equalities firstPureMaskTrace_range
    pcGenerator18_eq_kernelMask pcGenerator19_eq_kernelMask pcGenerator20_eq_kernelMask

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
