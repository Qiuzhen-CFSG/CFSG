module
public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.FieldTheory.Nine
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Explicit inversion witnesses in SU₃(3)

For the antidiagonal Hermitian form over the computable field of nine elements,
`regular` has order three and is inverted by the diagonal involution. A matrix
commuting with it is lower triangular with constant diagonal; determinant one
forces that diagonal to be one. Its two remaining parameters satisfy the
Hermitian equations, giving exactly nine centralizer elements.

The second witness `seven` has order seven and its inverse is its entrywise
quadratic conjugate. Four small matrix products certify its seventh power;
no enumeration of the full unitary group is used.

These are the concrete group calculations in Guralnick–Malle, *Classification
of 2F-modules I*, Proposition 4.3, manuscript pp.10–11. `GroupWitnesses.lean`
transports them to the literal derived binary G₂ group and its automorphisms.
-/

open Matrix BenderSuzuki.MatrixGroups
@[expose] public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.GroupWitnesses
abbrev F := FiniteField.Nine
abbrev Mat := Matrix (Fin 3) (Fin 3) F

def conjugation : F ≃+* F :=
  { starRingEnd F with
    invFun := star
    left_inv := star_involutive
    right_inv := star_involutive }
def form : HermitianForm 3 F where
  conj := conjugation
  conj_involutive := star_involutive
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by decide

def R : Mat := !![1,0,0; 1,1,0; 1,-1,1]
def Rinv : Mat := !![1,0,0; -1,1,0; 1,1,1]
def T : Mat := !![-1,0,0; 0,1,0; 0,0,-1]
def tau : F := ⟨0,1⟩
def M : Mat := !![1,1,1-tau; 1+tau,-1+tau,1; -1,1+tau,1]
def Mbar : Mat := M.map star

def Q : Mat := !![1-tau,tau-1,tau; tau+1,-1,tau-1; 1-tau,tau+1,1-tau]
def C : Mat := !![tau-1,tau,-1; 1-tau,0,tau; -tau,1-tau,tau-1]

theorem R_inverse : R * Rinv = 1 := by decide
theorem R_inverse' : Rinv * R = 1 := by decide
theorem R_square : R * R = Rinv := by decide
theorem R_preserves : form.conjTranspose R * form.form * R = form.form := by decide
theorem R_det : R.det = 1 := by decide
theorem T_square : T * T = 1 := by decide
theorem T_preserves : form.conjTranspose T * form.form * T = form.form := by decide
theorem T_det : T.det = 1 := by decide
theorem T_inverts_R : T * R * T = Rinv := by decide
theorem M_inverse : M * Mbar = 1 := by decide
theorem M_inverse' : Mbar * M = 1 := by decide
theorem M_preserves : form.conjTranspose M * form.form * M = form.form := by decide
theorem M_det : M.det = 1 := by decide
theorem M_square : M * M = Q := by decide
theorem M_cube_step : Q * M = C := by decide
theorem M_fourth_step : C * M = C.map star := by decide
theorem C_inverse : C * C.map star = 1 := by decide

theorem M_pow_seven : M ^ 7 = 1 := by
  have h3 : M ^ 3 = C := by
    rw [pow_succ, pow_two, M_square, M_cube_step]
  have h4 : M ^ 4 = C.map star := by
    rw [pow_succ, h3, M_fourth_step]
  rw [show (7 : ℕ) = 3 + 4 from rfl, pow_add, h3, h4, C_inverse]

abbrev SU := form.specialSubgroup

def regular : SU := ⟨⟨R, Rinv, R_inverse, R_inverse'⟩, by
  rw [form.mem_specialSubgroup_iff]
  exact ⟨R_preserves, Units.ext R_det⟩⟩
def involution : SU := ⟨⟨T, T, T_square, T_square⟩, by
  rw [form.mem_specialSubgroup_iff]
  exact ⟨T_preserves, Units.ext T_det⟩⟩
def seven : SU := ⟨⟨M, Mbar, M_inverse, M_inverse'⟩, by
  rw [form.mem_specialSubgroup_iff]
  exact ⟨M_preserves, Units.ext M_det⟩⟩

theorem regular_order : orderOf regular = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Units.ext
    change R ^ 3 = 1
    rw [pow_succ, pow_two, R_square, R_inverse']
  · intro h
    have he := congrArg (fun x : SU => x.val.val 1 0) h
    exact (by decide : (1 : F) ≠ 0) he

theorem involution_order : orderOf involution = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Units.ext
    change T ^ 2 = 1
    simpa only [pow_two] using T_square
  · intro h
    have he := congrArg (fun x : SU => x.val.val 0 0) h
    exact (by decide : (-1 : F) ≠ 1) he

theorem seven_order : orderOf seven = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Units.ext
    exact M_pow_seven
  · intro h
    have he := congrArg (fun x : SU => x.val.val 0 1) h
    exact (by decide : (1 : F) ≠ 0) he

theorem involution_inverts_regular : involution * regular * involution⁻¹ = regular⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  exact T_inverts_R

def lowerShape (a b c : F) : Mat := !![a,0,0; b,a,0; c,-b,a]
def centralMatrix (b c : F) : Mat := lowerShape 1 b c

private theorem commuting_shape (A : Mat) (h : A * R = R * A) :
    A = lowerShape (A 0 0) (A 1 0) (A 2 0) := by
  have h00 := congrArg (fun B : Mat => B 0 0) h
  have h01 := congrArg (fun B : Mat => B 0 1) h
  have h10 := congrArg (fun B : Mat => B 1 0) h
  have h11 := congrArg (fun B : Mat => B 1 1) h
  have h20 := congrArg (fun B : Mat => B 2 0) h
  have h21 := congrArg (fun B : Mat => B 2 1) h
  simp [R, Matrix.mul_apply, Fin.sum_univ_three] at h00 h01 h10 h11 h20 h21
  funext i j
  fin_cases i <;> fin_cases j <;> simp [lowerShape]
  · linear_combination h00 - h01
  · exact h01
  · linear_combination h10 + h11 + h00 - h01
  · linear_combination -h11 - h00 + h01
  · linear_combination h20 + h21 - h10 - h11
  · linear_combination h10 + h11 - h21

private theorem centralMatrix_preserves_iff (b c : F) :
    form.conjTranspose (centralMatrix b c) * form.form * centralMatrix b c = form.form ↔
      star b = b ∧ b * b + c + star c = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun A : Mat => A 0 1) h
    have h00 := congrArg (fun A : Mat => A 0 0) h
    simp [HermitianForm.conjTranspose, form, conjugation, starRingEnd_apply, centralMatrix, lowerShape,
      Matrix.mul_apply, Fin.sum_univ_three] at h01 h00
    have hb : star b = b := by linear_combination h01
    refine ⟨hb, ?_⟩
    rw [hb] at h00
    linear_combination h00
  · rintro ⟨hb, hc⟩
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, form, conjugation, starRingEnd_apply, centralMatrix, lowerShape,
        Matrix.mul_apply, Fin.sum_univ_three, hb]
    linear_combination hc

private def Parameters := {p : F × F // star p.1 = p.1 ∧ p.1 * p.1 + p.2 + star p.2 = 0}
private instance : Fintype Parameters := by unfold Parameters; infer_instance
private theorem parameters_card : Fintype.card Parameters = 9 := by decide

private def centralUnit (b c : F) : GL (Fin 3) F where
  val := centralMatrix b c
  inv := centralMatrix (-b) (-c-b*b)
  val_inv := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [centralMatrix, lowerShape, Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [centralMatrix, lowerShape, Matrix.mul_apply, Fin.sum_univ_three]

private theorem centralMatrix_commutes (b c : F) :
    centralMatrix b c * R = R * centralMatrix b c := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralMatrix, lowerShape, R, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private def fromParameters (p : Parameters) : Subgroup.centralizer ({regular} : Set SU) :=
  ⟨⟨centralUnit p.val.1 p.val.2, by
    rw [form.mem_specialSubgroup_iff]
    refine ⟨(centralMatrix_preserves_iff _ _).2 p.property, ?_⟩
    apply Units.ext
    simp [centralUnit, centralMatrix, lowerShape, Matrix.det_fin_three]⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    exact centralMatrix_commutes _ _⟩

private theorem centralizer_shape (x : Subgroup.centralizer ({regular} : Set SU)) :
    x.val.val.val = centralMatrix (x.val.val.val 1 0) (x.val.val.val 2 0) := by
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp x.property
  have hs := commuting_shape x.val.val.val (congrArg (fun y : SU => y.val.val) hcomm)
  have hd := congrArg Units.val x.val.property.2
  change x.val.val.val.det = 1 at hd
  rw [hs] at hd
  have hd' : (x.val.val.val 0 0) ^ 3 = 1 := by
    simpa [lowerShape, Matrix.det_fin_three, pow_succ] using hd
  have ha : x.val.val.val 0 0 = 1 :=
    (show ∀ a : F, a ^ 3 = 1 → a = 1 by decide) _ hd'
  simpa only [ha, centralMatrix] using hs

private def toParameters (x : Subgroup.centralizer ({regular} : Set SU)) : Parameters :=
  ⟨(x.val.val.val 1 0, x.val.val.val 2 0), by
    apply (centralMatrix_preserves_iff _ _).1
    rw [← centralizer_shape x]
    exact x.val.property.1⟩

private def centralizerEquivParameters : Subgroup.centralizer ({regular} : Set SU) ≃ Parameters where
  toFun := toParameters
  invFun := fromParameters
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact (centralizer_shape x).symm
  right_inv p := by
    apply Subtype.ext
    rfl

theorem regular_centralizer_card : Nat.card (Subgroup.centralizer ({regular} : Set SU)) = 9 := by
  rw [Nat.card_congr centralizerEquivParameters, Nat.card_eq_fintype_card, parameters_card]

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.GroupWitnesses
