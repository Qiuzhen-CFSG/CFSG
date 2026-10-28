module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.ColumnDuality
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.OuterProjective
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.PairQuintet
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Structure

/-!
# Assembly of the reference-vector comparison

The cubic-scalar quotient is injective on a nonzero binary point stabilizer.
The explicit Gram matrix converts column vector 1327 to published row 2045,
whose endpoint pair is {11,19}. Consequently two independent geometric
comparisons finish the required carrier equivalence: the outer row action
matches the native degree-22 projection at this pair, and the native pair
stabilizer is geometrically identified with the source-marked quintet.

The unconditional `referencePointCentralizerEquiv` assembles these proved
comparisons on the literal binary vector stabilizer in the full outer matrix
extension. Its projection equation retains the actual degree-22 action.
The parent centralizer module supplies the intrinsic two-core and Borel
transport and is deliberately not imported here.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012, and H.12.1(5,9),
printed pp.393--394, with the quintet setup and local in H.14, printed
pp.396--397 (1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- Conditional assembly retains the literal binary stabilizer and the
source-marked quintet. The unconditional construction below supplies both
geometric comparisons. -/
def referencePointCentralizerEquivOfComparisons
    (hrow : ∀ g : Model,
      Matrix.vecMul (projectiveVector 228) ((g.val⁻¹ : Matrix12ˣ) : Matrix12) ∈
          scalarLine (projectiveVector 228) ↔
        referenceProjection g ∈ referencePairStabilizer referencePair)
    (e : referencePairStabilizer referencePair ≃* MathieuCode.M22Quintet.Q) :
    pointCentralizer referenceVector ≃* MathieuCode.M22Quintet.Q :=
  (referencePointCentralizerEquivPair referencePair
    (fun g => (reference_projective_comparison g).trans (hrow g))).trans e

/-- The binary column-vector stabilizer of packed vector 1327 in the literal
outer matrix extension is the native source-marked quintet group. -/
def referencePointCentralizerEquiv :
    pointCentralizer referenceVector ≃* MathieuCode.M22Quintet.Q :=
  referencePointCentralizerEquivOfComparisons
    referenceRowPairComparison referencePairQuintetEquiv

/-- Comparing back through the geometric quintet equivalence recovers the
actual degree-22 projection of every binary stabilizer element. -/
@[simp] theorem referencePointCentralizerEquiv_projection (x : pointCentralizer referenceVector) :
    (referencePairQuintetEquiv.symm (referencePointCentralizerEquiv x)).val =
      referenceProjection x.val := by
  simp only [referencePointCentralizerEquiv, referencePointCentralizerEquivOfComparisons,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, referencePointCentralizerEquivPair_apply]

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
