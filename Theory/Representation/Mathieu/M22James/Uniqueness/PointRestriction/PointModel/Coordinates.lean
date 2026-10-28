module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.Invariant
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ReferenceData

/-!
# A checked coordinate change on the whole point-restriction space

The displayed binary matrix and its inverse give an actual linear equivalence
on all twelve dimensions. It carries the geometric invariant submodule, with
its specified three field columns, onto the first coordinate block of the
reference space. Equivariance with the reference operators is not assumed.

The matrix was found by solving simultaneous intertwining equations for the
ATLAS-derived stabilizer words. Only its inverse identities and its action on
the invariant subspace are asserted here; they are checked by the Lean kernel.
The original matrix attribution is retained in the J₄ `LinearModel/source/`
directory. Source context: James (1973), Lemma 8.3, used in H.12.1(1),
Aschbacher–Smith, printed pp.393–394.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix

/-- Binary coordinates on the two three-dimensional field coordinate blocks. -/
def flattenPair : Reference.V ≃ₗ[ZMod 2] BinarySpace where
  toFun v := ![(v.1 0).re, (v.1 0).im, (v.1 1).re, (v.1 1).im, (v.1 2).re, (v.1 2).im,
    (v.2 0).re, (v.2 0).im, (v.2 1).re, (v.2 1).im, (v.2 2).re, (v.2 2).im]
  invFun v := (![⟨v 0, v 1⟩, ⟨v 2, v 3⟩, ⟨v 4, v 5⟩],
    ![⟨v 6, v 7⟩, ⟨v 8, v 9⟩, ⟨v 10, v 11⟩])
  left_inv v := by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' a v := by funext i; fin_cases i <;> rfl

/-- A candidate change of coordinates on the entire literal binary module. -/
def comparisonMatrix : Matrix12 :=
  fromRows ![865, 853, 2076, 2267, 2567, 3577, 2288, 1821, 2348, 868, 684, 3142]

/-- The checked inverse matrix for the full-space comparison. -/
def comparisonInverse : Matrix12 :=
  fromRows ![1534, 2105, 2047, 2764, 191, 1859, 996, 2512, 1784, 1952, 2474, 3464]

set_option maxRecDepth 4000 in
private lemma comparison_left : comparisonInverse * comparisonMatrix = 1 := by decide +kernel

set_option maxRecDepth 4000 in
private lemma comparison_right : comparisonMatrix * comparisonInverse = 1 := by decide +kernel

/-- The full coordinate change before decoding the two field blocks. -/
def binaryComparison : BinarySpace ≃ₗ[ZMod 2] BinarySpace :=
  { comparisonMatrix.mulVecLin with
    invFun := fun v => comparisonInverse *ᵥ v
    left_inv := fun v => by
      change comparisonInverse *ᵥ (comparisonMatrix *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, comparison_left, Matrix.one_mulVec]
    right_inv := fun v => by
      change comparisonMatrix *ᵥ (comparisonInverse *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, comparison_right, Matrix.one_mulVec] }

/-- An actual linear equivalence on all twelve binary dimensions.
Equivariance is a separate obligation; this definition assumes no group comparison. -/
def coordinates : BinarySpace ≃ₗ[ZMod 2] Reference.V :=
  binaryComparison.trans flattenPair.symm

lemma coordinates_apply (v : BinarySpace) :
    flattenPair (coordinates v) = comparisonMatrix *ᵥ v := flattenPair.apply_symm_apply _

private def firstBlock : Matrix (Fin 12) (Fin 6) (ZMod 2) :=
  fun i j => if i.val = j.val then 1 else 0

set_option maxRecDepth 4000 in
private lemma comparison_inclusion : comparisonMatrix * inclusionMatrix = firstBlock := by
  decide +kernel

/-- The specified coordinates carry the actual geometric submodule to the first block. -/
lemma coordinates_inclusion (v : Fin 3 → F) : coordinates (naturalInclusion v) = (v,0) := by
  apply flattenPair.injective
  rw [coordinates_apply, naturalInclusion_apply, Matrix.mulVec_mulVec, comparison_inclusion]
  funext i
  fin_cases i <;>
    simp [firstBlock, flattenPair, flatten, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
