module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.Natural
/-!
# Natural rank-one maps in the split orthogonal eight-space

The right determinant action, reparametrized by inverse transpose, gives the
three difference roots. Conjugation by diag(-1,1) in the left determinant
action gives the sum root. Transport of the first difference root cycles three
hyperbolic pairs to give the central root. All maps land in the actual
Siegel-generated carrier through the elementary block and isometry maps.
The coordinate formulas retain the fixed signs of the integral Geck comparison.

Sources: GLS3 §§2.4, 2.6–2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[expose] public section
open Matrix
open scoped MatrixGroups
open ClassicalOrthogonal ClassicalOrthogonal.Fundamental ClassicalOrthogonal.Fundamental.SplitOddBlocks
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.PinningConstruction
noncomputable section
variable {F : Type*} [Field F]

/-- Inverse transpose, as an automorphism of SL₂. -/
def dual : SL(2,F) ≃* SL(2,F) where
  toFun a := SpecialLinearGroup.transpose a⁻¹
  invFun a := SpecialLinearGroup.transpose a⁻¹
  left_inv a := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_transpose, Matrix.adjugate_fin_two]
  right_inv a := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_transpose, Matrix.adjugate_fin_two]
  map_mul' a b := by
    apply Subtype.ext
    change ((a * b)⁻¹).val.transpose = a⁻¹.val.transpose * b⁻¹.val.transpose
    rw [_root_.mul_inv_rev]
    exact Matrix.transpose_mul _ _

/-- Conjugation by diag(-1,1), requiring no square root of minus one. -/
def sign : SL(2,F) ≃* SL(2,F) where
  toFun a := ⟨!![a 0 0, -a 0 1; -a 1 0, a 1 1], by
    rw [Matrix.det_fin_two]
    change a 0 0 * a 1 1 - (-a 0 1) * (-a 1 0) = 1
    rw [neg_mul_neg]
    exact (Matrix.det_fin_two a.val) ▸ a.prop⟩
  invFun a := ⟨!![a 0 0, -a 0 1; -a 1 0, a 1 1], by
    rw [Matrix.det_fin_two]
    change a 0 0 * a 1 1 - (-a 0 1) * (-a 1 0) = 1
    rw [neg_mul_neg]
    exact (Matrix.det_fin_two a.val) ▸ a.prop⟩
  left_inv a := by ext i j; fin_cases i <;> fin_cases j <;> simp
  right_inv a := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def arm0 : SL(2,F) →* OmegaPlus 4 F :=
  (rightCover (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm).comp
    ((MonoidHom.inl _ _).comp dual.toMonoidHom)
def arm2 : SL(2,F) →* OmegaPlus 4 F :=
  (rightCover (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm).comp
    ((MonoidHom.inr _ _).comp (fourRight.comp dual.toMonoidHom))
def arm3 : SL(2,F) →* OmegaPlus 4 F :=
  (rightCover (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm).comp
    ((MonoidHom.inr _ _).comp (fourLeft.comp sign.toMonoidHom))

theorem arm0_apply (a : SL(2,F)) (v : VectorD 4 F) :
    (arm0 a).val.val v = Sum.elim
      ![a 0 0 * v (.inl 0) + a 0 1 * v (.inl 1),
        a 1 0 * v (.inl 0) + a 1 1 * v (.inl 1), v (.inl 2), v (.inl 3)]
      ![a 1 1 * v (.inr 0) - a 1 0 * v (.inr 1),
        -(a 0 1 * v (.inr 0)) + a 0 0 * v (.inr 1), v (.inr 2), v (.inr 3)] := by
  change (splitD (F := F) 2 2).symm
    (FourPlusMatrix.coordinates.symm ((1 : SL(2,F)).val *
      FourPlusMatrix.coordinates ((splitD 2 2 v).1) * (dual a)⁻¹.val),
      (1 : OmegaPlus 2 F).val.val ((splitD 2 2 v).2)) = _
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [splitD, FourPlusMatrix.coordinates, dual, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.addCases]
    <;> ring

theorem arm2_apply (a : SL(2,F)) (v : VectorD 4 F) :
    (arm2 a).val.val v = Sum.elim
      ![v (.inl 0), v (.inl 1), a 0 0 * v (.inl 2) + a 0 1 * v (.inl 3),
        a 1 0 * v (.inl 2) + a 1 1 * v (.inl 3)]
      ![v (.inr 0), v (.inr 1), a 1 1 * v (.inr 2) - a 1 0 * v (.inr 3),
        -(a 0 1 * v (.inr 2)) + a 0 0 * v (.inr 3)] := by
  change (splitD (F := F) 2 2).symm
    ((fourRight (1 : SL(2,F))).val.val ((splitD 2 2 v).1),
      FourPlusMatrix.coordinates.symm ((1 : SL(2,F)).val *
        FourPlusMatrix.coordinates ((splitD 2 2 v).2) * (dual a)⁻¹.val)) = _
  rw [map_one]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [splitD, FourPlusMatrix.coordinates, dual, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.addCases] <;> ring

theorem arm3_apply (a : SL(2,F)) (v : VectorD 4 F) :
    (arm3 a).val.val v = Sum.elim
      ![v (.inl 0), v (.inl 1), a 0 0 * v (.inl 2) + a 0 1 * v (.inr 3),
        a 0 0 * v (.inl 3) - a 0 1 * v (.inr 2)]
      ![v (.inr 0), v (.inr 1), -(a 1 0 * v (.inl 3)) + a 1 1 * v (.inr 2),
        a 1 0 * v (.inl 2) + a 1 1 * v (.inr 3)] := by
  change (splitD (F := F) 2 2).symm
    ((fourRight (1 : SL(2,F))).val.val ((splitD 2 2 v).1),
      FourPlusMatrix.coordinates.symm ((sign a).val *
        FourPlusMatrix.coordinates ((splitD 2 2 v).2) * (1 : SL(2,F))⁻¹.val)) = _
  rw [map_one]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [splitD, FourPlusMatrix.coordinates, sign,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.addCases] <;> ring

/-- Cycle the first three hyperbolic pairs, sending the pair (0,1) to (1,2). -/
def rotate : (formD 4 F).IsometryEquiv (formD 4 F) where
  toFun v := Sum.elim ![v (.inl 2), v (.inl 0), v (.inl 1), v (.inl 3)]
    ![v (.inr 2), v (.inr 0), v (.inr 1), v (.inr 3)]
  invFun v := Sum.elim ![v (.inl 1), v (.inl 2), v (.inl 0), v (.inl 3)]
    ![v (.inr 1), v (.inr 2), v (.inr 0), v (.inr 3)]
  left_inv v := by funext k; rcases k with k | k <;> fin_cases k <;> rfl
  right_inv v := by funext k; rcases k with k | k <;> fin_cases k <;> rfl
  map_add' v w := by funext k; rcases k with k | k <;> fin_cases k <;> rfl
  map_smul' t v := by funext k; rcases k with k | k <;> fin_cases k <;> rfl
  map_app' v := by simp [formD_apply, Fin.sum_univ_four]; ring

def central : SL(2,F) →* OmegaPlus 4 F :=
  (elementaryConjugate (rotate (F := F))).comp arm0

theorem central_apply (a : SL(2,F)) (v : VectorD 4 F) :
    (central a).val.val v = Sum.elim
      ![v (.inl 0), a 0 0 * v (.inl 1) + a 0 1 * v (.inl 2),
        a 1 0 * v (.inl 1) + a 1 1 * v (.inl 2), v (.inl 3)]
      ![v (.inr 0), a 1 1 * v (.inr 1) - a 1 0 * v (.inr 2),
        -(a 0 1 * v (.inr 1)) + a 0 0 * v (.inr 2), v (.inr 3)] := by
  change rotate ((arm0 a).val.val (rotate.symm v)) = _
  rw [arm0_apply]
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

end
end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.PinningConstruction
