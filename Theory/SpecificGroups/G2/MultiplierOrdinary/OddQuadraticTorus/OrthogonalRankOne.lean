module
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

/-!
# Two orthogonal rank-one factors in the octonion G₂ model

Wilson's coordinates identify the split octonions with pairs (a,b) of 2×2
matrices. Quaternion conjugation is the adjugate, and multiplication is
(ac − d̄b, da + bc̄). Determinant-one matrices act by
(a,b) ↦ (AaA⁻¹, BbA⁻¹). This preserves the literal octonion product and
gives a homomorphism SL₂ × SL₂ → G₂ over every field.

A trivial action makes B=A and forces A to commute with the matrix units.
The determinant then gives A=±I. Thus the kernel is exactly the common
scalar signs, rather than a faithful direct product. Its exponent-two
consequence is consumed by the quadratic norm-one torus transfer argument.

Source: the standard split-quaternion construction of the orthogonal
rank-one subgroup, used in the covering calculations of Aschbacher–Smith
I.1.1–4 and GLS III §6.1. Coordinates use the licensed ATLAS split-octonion
model, Wilson's integral table (Eq. 4.11); see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. The coordinate comparison and matrix action
are verified directly here, without a group-order or recognition premise.
-/

@[expose] public section
namespace Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
open Atlas.SplitOctonion Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F]

abbrev Mat (F : Type*) := Matrix (Fin 2) (Fin 2) F

/-- Quaternion conjugation in the split matrix algebra. -/
def bar (a : Mat F) : Mat F := !![a 1 1, -a 0 1; -a 1 0, a 0 0]

theorem bar_mul (a b : Mat F) : bar (a*b) = bar b * bar a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bar, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bar_bar (a : Mat F) : bar (bar a) = a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bar]

theorem bar_one : bar (1 : Mat F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bar]

theorem sl_mul_bar (A : SL(2,F)) : A.val * bar A.val = 1 := by
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bar, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | (solve | ring) | linear_combination hd

theorem sl_bar_mul (A : SL(2,F)) : bar A.val * A.val = 1 := by
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bar, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | (solve | ring) | linear_combination hd

/-- The quaternion subalgebra and its complement in Wilson's coordinates. -/
def coordinates : Carrier F ≃ₗ[F] (Mat F × Mat F) where
  toFun x := (!![x 3,x 0; -x 7,x 4], !![x 6,-x 2; x 5,x 1])
  invFun z := ![z.1 0 1,z.2 1 1,-z.2 0 1,z.1 0 0,z.1 1 1,z.2 1 0,z.2 0 0,-z.1 1 0]
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv z := by
    apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp
  map_add' x y := by
    apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r x := by
    apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-- Cayley–Dickson multiplication with the chosen norm-one complementary vector. -/
def pairMul (x y : Mat F × Mat F) : Mat F × Mat F :=
  (x.1*y.1 - bar y.2*x.2, y.2*x.1 + x.2*bar y.1)

theorem coordinates_mul (x y : Carrier F) :
    coordinates (mul x y) = pairMul (coordinates x) (coordinates y) := by
  apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [coordinates, mul, pairMul, bar] <;> ring

/-- The two determinant-one matrix factors on the quaternion decomposition. -/
def pairLinear (A B : SL(2,F)) : (Mat F × Mat F) →ₗ[F] (Mat F × Mat F) where
  toFun x := (A.val*x.1*bar A.val, B.val*x.2*bar A.val)
  map_add' x y := by simp [_root_.mul_add, _root_.add_mul]
  map_smul' r x := by simp

theorem pairLinear_mul (A B C D : SL(2,F)) (x : Mat F × Mat F) :
    pairLinear (A*C) (B*D) x = pairLinear A B (pairLinear C D x) := by
  change ((A.val*C.val)*x.1*bar (A.val*C.val),
    (B.val*D.val)*x.2*bar (A.val*C.val)) = _
  simp [pairLinear, bar_mul, mul_assoc]

theorem pairLinear_one (x : Mat F × Mat F) : pairLinear 1 1 x = x := by
  simp [pairLinear, bar_one]

theorem pairLinear_preserves (A B : SL(2,F)) (x y : Mat F × Mat F) :
    pairLinear A B (pairMul x y) = pairMul (pairLinear A B x) (pairLinear A B y) := by
  simp only [pairLinear, LinearMap.coe_mk, AddHom.coe_mk, pairMul, bar_mul, bar_bar]
  apply Prod.ext
  · dsimp only
    simp only [mul_sub, sub_mul]
    simp only [mul_assoc, ← mul_assoc (bar A.val) A.val, sl_bar_mul, one_mul,
      ← mul_assoc (bar B.val) B.val]
  · dsimp only
    simp only [_root_.mul_add, _root_.add_mul]
    simp only [mul_assoc, ← mul_assoc (bar A.val) A.val, sl_bar_mul, one_mul]

def pairEquiv (A B : SL(2,F)) : (Mat F × Mat F) ≃ₗ[F] (Mat F × Mat F) where
  toLinearMap := pairLinear A B
  invFun := pairLinear A⁻¹ B⁻¹
  left_inv x := by
    change pairLinear A⁻¹ B⁻¹ (pairLinear A B x) = x
    rw [← pairLinear_mul, inv_mul_cancel, inv_mul_cancel, pairLinear_one]
  right_inv x := by
    change pairLinear A B (pairLinear A⁻¹ B⁻¹ x) = x
    rw [← pairLinear_mul, mul_inv_cancel, mul_inv_cancel, pairLinear_one]

def octonionEquiv (A B : SL(2,F)) : Carrier F ≃ₗ[F] Carrier F :=
  coordinates.trans ((pairEquiv A B).trans coordinates.symm)

theorem octonionEquiv_preserves (A B : SL(2,F)) (x y : Carrier F) :
    octonionEquiv A B (mul x y) = mul (octonionEquiv A B x) (octonionEquiv A B y) := by
  apply coordinates.injective
  simp only [octonionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    coordinates_mul]
  exact pairLinear_preserves A B _ _

/-- The genuine central-product homomorphism into the octonion automorphism group. -/
def productHom : (SL(2,F) × SL(2,F)) →* Model F where
  toFun x := ⟨octonionEquiv x.1 x.2, octonionEquiv_preserves x.1 x.2⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply coordinates.injective
    simp only [octonionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact pairLinear_one _
  map_mul' x y := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    apply coordinates.injective
    change coordinates (octonionEquiv (x.1*y.1) (x.2*y.2) z) =
      coordinates (octonionEquiv x.1 x.2 (octonionEquiv y.1 y.2 z))
    simp only [octonionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact pairLinear_mul _ _ _ _ _

/-- A trivial octonion action is a trivial action on both quaternion coordinates. -/
theorem kernel_action (A B : SL(2,F)) (h : productHom (A,B) = 1)
    (x : Mat F × Mat F) : pairLinear A B x = x := by
  have he := congrArg (fun g : Model F => coordinates (g.val (coordinates.symm x))) h
  change coordinates (octonionEquiv A B (coordinates.symm x)) =
    coordinates (coordinates.symm x) at he
  simpa only [octonionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    pairEquiv, LinearEquiv.coe_mk] using he

/-- The only kernel matrices are equal scalar matrices with square one. -/
theorem kernel_scalar (A B : SL(2,F)) (h : productHom (A,B) = 1) :
    B = A ∧ A.val 0 1 = 0 ∧ A.val 1 0 = 0 ∧
      A.val 0 0 = A.val 1 1 ∧ A.val 0 0 ^ 2 = 1 := by
  have hB : B = A := by
    have he := congrArg Prod.snd (kernel_action A B h (0,1))
    change B.val * 1 * bar A.val = 1 at he
    have hh := congrArg (fun M : Mat F => M * A.val) he
    apply Subtype.ext
    simpa only [mul_one, mul_assoc, sl_bar_mul, one_mul] using hh
  have hcomm (X : Mat F) : A.val * X = X * A.val := by
    have he := congrArg Prod.fst (kernel_action A B h (X,0))
    change A.val * X * bar A.val = X at he
    have hh := congrArg (fun M : Mat F => M * A.val) he
    simpa only [mul_assoc, sl_bar_mul, mul_one] using hh
  have h01 : A.val 0 1 = 0 := by
    have he := congrArg (fun M : Mat F => M 0 1) (hcomm !![1,0;0,0])
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using he.symm
  have h10 : A.val 1 0 = 0 := by
    have he := congrArg (fun M : Mat F => M 1 0) (hcomm !![1,0;0,0])
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
  have h00 : A.val 0 0 = A.val 1 1 := by
    have he := congrArg (fun M : Mat F => M 0 1) (hcomm !![0,1;0,0])
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
  refine ⟨hB,h01,h10,h00,?_⟩
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  simpa only [h01, h10, ← h00, mul_zero, sub_zero, pow_two] using hd

/-- The central-product kernel has exponent two, including in odd characteristic. -/
theorem productHom_kernel_square (a : SL(2,F) × SL(2,F))
    (ha : productHom a = 1) : a ^ 2 = 1 := by
  rcases a with ⟨A,B⟩
  obtain ⟨hB,h01,h10,h00,hsq⟩ := kernel_scalar A B ha
  subst B
  have hA : A ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    change A.val * A.val = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, ← h00, ← pow_two, hsq]
  exact Prod.ext hA hA

/-- Both central minus identities act trivially together. -/
theorem productHom_neg_one : productHom (-1, -1) = (1 : Model F) := by
  have hb : bar (-1 : Mat F) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bar]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply coordinates.injective
  change coordinates (octonionEquiv (-1) (-1) x) = coordinates x
  simp only [octonionEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change pairLinear (-1) (-1) (coordinates x) = coordinates x
  simp [pairLinear, hb]

/-- The exact common central kernel, without an injectivity assumption. -/
theorem productHom_eq_one_iff (a : SL(2,F) × SL(2,F)) :
    productHom a = 1 ↔ a = 1 ∨ a = (-1,-1) := by
  constructor
  · rcases a with ⟨A,B⟩
    intro ha
    obtain ⟨hB,h01,h10,h00,hsq⟩ := kernel_scalar A B ha
    subst B
    rcases sq_eq_one_iff.mp hsq with h | h
    · have hA : A = 1 := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01,h10,← h00,h]
      simp [hA]
    · have hA : A = -1 := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01,h10,← h00,h]
      simp [hA]
  · rintro (rfl | rfl)
    · exact map_one productHom
    · exact productHom_neg_one

end Atlas.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
end
