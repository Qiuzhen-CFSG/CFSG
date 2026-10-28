module
public import Theory.Combinatorics.TranslationPlane.NativeFlagRoots

/-!
# Full native flag elations and normality of the matrix action

For each incident center and axis, the matrices I+a(v wᵀ) are q distinct
elations. The geometric evaluation bound makes their flag group the full
collineation flag group. Elementary generation then proves that the native
SL₃ image is normal in the complete incidence collineation group, without
using the classification of semilinear collineations. This includes q=2.

Source: DGS, Groups and Graphs, Theorem D, printed p.224; Steinberg,
Lectures on Chevalley Groups, Section 6. Used by A2Source/RootGeneration.
-/

@[expose] public noncomputable section
namespace Configuration.TranslationPlane.FieldChart
open Matrix Projectivization Theory.SpecificGroups.LinearHigher
open scoped MatrixGroups
variable {F : Type*} [Field F]

/-- A transvection with the specified center vector and axis covector. -/
def flagMatrix (v w : Fin 3 → F) (hvw : v ⬝ᵥ w = 0) (a : F) : SL(3,F) :=
  ⟨1 + a • vecMulVec v w,by
    have hd : det (1 + a • vecMulVec v w) = 1 + a * (v ⬝ᵥ w) := by
      simp [det_fin_three,vecMulVec,dotProduct,Fin.sum_univ_three]
      ring
    rw [hd,hvw,mul_zero,add_zero]⟩

theorem flagMatrix_mulVec (v w : Fin 3 → F) (hvw : v ⬝ᵥ w = 0) (a : F) (t : Fin 3 → F) :
    (flagMatrix v w hvw a).val *ᵥ t = t + (a * (w ⬝ᵥ t)) • v := by
  simp only [flagMatrix,add_mulVec,one_mulVec,smul_mulVec,vecMulVec_mulVec]
  ext i
  simp [mul_comm,mul_left_comm]

theorem flagMatrix_inv (v w : Fin 3 → F) (hvw : v ⬝ᵥ w = 0) (a : F) :
    (flagMatrix v w hvw a)⁻¹ = flagMatrix v w hvw (-a) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (1 + a • vecMulVec v w) * (1 + (-a) • vecMulVec v w) = 1
  have hwv : w ⬝ᵥ v = 0 := by rw [dotProduct_comm,hvw]
  simp [mul_add,add_mul,vecMulVec_mul_vecMulVec,hwv]

theorem flagMatrix_mem_flagElations (v w : Fin 3 → F) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : v ⬝ᵥ w = 0) (a : F) :
    specialLinearCollineation (flagMatrix v w hvw a) ∈
      flagElations (mk F v hv) (mk F w hw) := by
  constructor
  · intro p hp
    induction p using Projectivization.ind with | h t ht =>
    have htw : w ⬝ᵥ t = 0 := by
      rw [dotProduct_comm]
      exact (orthogonal_mk _ _).mp hp
    rw [specialLinearCollineation_point,smul_mk]
    have he : flagMatrix v w hvw a • t = t := by
      change (flagMatrix v w hvw a).val *ᵥ t = t
      simp [flagMatrix_mulVec,htw]
    exact congrArg (fun x : {v : Fin 3 → F // v ≠ 0} => mk' F x) (Subtype.ext he)
  · intro l hl
    induction l using Projectivization.ind with | h t ht =>
    have hvt : v ⬝ᵥ t = 0 := (orthogonal_mk _ _).mp hl
    rw [specialLinearCollineation_line,smul_mk]
    have he : SpecialLinearGroup.inverseTranspose (flagMatrix v w hvw a) • t = t := by
      change (flagMatrix v w hvw a)⁻¹.val.transpose *ᵥ t = t
      rw [flagMatrix_inv]
      change (1 + (-a) • vecMulVec v w).transpose *ᵥ t = t
      simp [transpose_add,transpose_smul,transpose_vecMulVec,add_mulVec,
        neg_mulVec,smul_mulVec,vecMulVec_mulVec,hvt]
    exact congrArg (fun x : {v : Fin 3 → F // v ≠ 0} => mk' F x) (Subtype.ext he)

theorem flagMatrix_action_injective (v w : Fin 3 → F) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : v ⬝ᵥ w = 0) :
    Function.Injective (fun a : F => specialLinearCollineation (flagMatrix v w hvw a)) := by
  intro a b he
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hw
  change w j ≠ 0 at hj
  let t : Fin 3 → F := Pi.single j 1
  have ht : t ≠ 0 := by intro hh; have := congrFun hh j; simp [t] at this
  have hp := congrArg (fun g => Collineation.pointHom _ _ g (mk F t ht)) he
  simp only [specialLinearCollineation_point,smul_mk] at hp
  obtain ⟨r,hr⟩ := (mk_eq_mk_iff' F _ _ _ _).mp hp
  change r • ((flagMatrix v w hvw b).val *ᵥ t) = (flagMatrix v w hvw a).val *ᵥ t at hr
  symm at hr
  rw [flagMatrix_mulVec,flagMatrix_mulVec] at hr
  have hwv : w ⬝ᵥ v = 0 := by rw [dotProduct_comm,hvw]
  have hr1 : r = 1 := by
    have hh := congrArg (fun x => w ⬝ᵥ x) hr
    simp [dotProduct_add,dotProduct_smul,hwv,t,dotProduct_single] at hh
    exact (mul_eq_left₀ hj).mp (by simpa [mul_comm] using hh.symm)
  rw [hr1,one_smul] at hr
  have hab : a * w j = b * w j := by
    apply smul_left_injective F hv
    simpa only [t,dotProduct_single,mul_one] using add_left_cancel hr
  exact mul_right_cancel₀ hj hab

variable [Finite F]
local instance : DecidableEq F := Classical.decEq F

/-- The order of the native plane is the cardinality of its field. -/
theorem plane_order : ProjectivePlane.order (PG F) (PG F) = Nat.card F := by
  have hc := Nat.card_congr (chart F)
  rw [Nat.card_fun,Nat.card_fin,card_affinePoints] at hc
  nlinarith

/-- Every geometric elation of an incident native flag is induced by a determinant-one matrix. -/
theorem flagElations_le_specialLinear_range (C l : PG F) (hCl : C ∈ l) :
    flagElations C l ≤ (specialLinearCollineation (K := F)).range := by
  induction C using Projectivization.ind with | h v hv =>
  induction l using Projectivization.ind with | h w hw =>
  have hvw : v ⬝ᵥ w = 0 := (orthogonal_mk _ _).mp hCl
  let R := flagElations (mk F v hv) (mk F w hw) ⊓
    (specialLinearCollineation (K := F)).range
  let f : F → R := fun a => ⟨specialLinearCollineation (flagMatrix v w hvw a),
    flagMatrix_mem_flagElations v w hv hw hvw a,⟨_,rfl⟩⟩
  have hinj : Function.Injective f := fun a b he =>
    flagMatrix_action_injective v w hv hw hvw (congrArg Subtype.val he)
  have hc : Nat.card F ≤ Nat.card R := Nat.card_le_card_of_injective f hinj
  obtain ⟨o,ho⟩ := Nondegenerate.exists_point (P := PG F) (mk F w hw)
  have hbound := flagElations_card_le (mk F v hv) (mk F w hw) hCl o ho
  rw [plane_order] at hbound
  have he : R = flagElations (mk F v hv) (mk F w hw) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (hbound.trans hc)
  exact he ▸ inf_le_right

/-- The matrix collineation image is invariant under every incidence collineation.
Elementary generation and the full geometric flag groups avoid semilinear classification. -/
theorem specialLinear_range_normal : (specialLinearCollineation (K := F)).range.Normal := by
  constructor
  rintro g ⟨A,rfl⟩ a
  apply Atlas.sl_elementary_induction
    (fun A : SL(3,F) => a * specialLinearCollineation A * a⁻¹ ∈
      (specialLinearCollineation (K := F)).range)
  · intro i j hij t
    exact flagElations_le_specialLinear_range
      (Collineation.pointHom _ _ a (coordinate F i))
      (Collineation.lineHom _ _ a (coordinate F j))
      ((Collineation.mem_iff a _ _).mpr (coordinate_incident F hij))
      ((flagElations_conjugate_mem_iff _ _ a _).mpr
        (matrixRoot_mem_flagElations F (root i j hij) t))
  · intro A B hA hB
    have he : a * specialLinearCollineation (A * B) * a⁻¹ =
        (a * specialLinearCollineation A * a⁻¹) *
          (a * specialLinearCollineation B * a⁻¹) := by rw [map_mul]; group
    rw [he]
    exact Subgroup.mul_mem _ hA hB

end Configuration.TranslationPlane.FieldChart
