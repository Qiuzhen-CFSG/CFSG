module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Faithfulness and the finite Hermitian action image

The action of SL₂ on the Hermitian matrix space is faithful in characteristic
two. An element in its kernel fixes the two diagonal matrix units, forcing its
off-diagonal entries to vanish. Fixing the Hermitian matrix with off-diagonal
entries one, together with determinant one, forces a diagonal entry to be fixed
by conjugation. Its norm is one, so its square is one, and characteristic two
forces both diagonal entries to be one.

The image is an actual subgroup of the linear automorphisms of `Space n`.
Its natural action agrees with the previously defined matrix action and
preserves the determinant form. The scalar description of the SL₂ center
shows that it is trivial; consequently the quotient map identifies SL₂ with
PSL₂ and hence identifies PSL₂ with this same action image. These results
include `n = 1`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419), and the
standard scalar description of the center of a special linear group.
-/

@[expose] public section

noncomputable section
namespace Representation.OrthogonalFourMinus.FiniteModel

private lemma eq_one_of_action_eq_one (n : ℕ) [NeZero n]
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (hA : action n A = 1) : A = 1 := by
  have h (v : (fixedField n × fixedField n) × Field n) (i j : Fin 2) :
      (A.val * !![v.1.1.val, v.2; conjugation n v.2, v.1.2.val] *
        adjoint (conjugation n) A.val) i j =
      (!![v.1.1.val, v.2; conjugation n v.2, v.1.2.val] : Mat (Field n)) i j := by
    have he := congrArg (fun f : Space n →ₗ[fixedField n] Space n =>
      (f ((coordinates n).symm v)).val i j) hA
    simpa only [action_apply, coordinates_symm_val, Module.End.one_apply] using he
  have hc : A.val 1 0 = 0 := by
    have he := h ((1, 0), 0) 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint] using he
  have hb : A.val 0 1 = 0 := by
    have he := h ((0, 1), 0) 0 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint] using he
  have hd : A.val 1 1 * conjugation n (A.val 1 1) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint] using h ((0, 1), 0) 1 1
  have had : A.val 0 0 * A.val 1 1 = 1 := by
    have he : A.val.det = 1 := A.property
    rwa [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at he
  have had' : A.val 0 0 * conjugation n (A.val 1 1) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint, hb, hc] using h ((0, 0), 1) 0 1
  have ha0 : A.val 0 0 ≠ 0 := by
    intro hz
    simp [hz] at had
  have hdf : conjugation n (A.val 1 1) = A.val 1 1 :=
    mul_left_cancel₀ ha0 (had'.trans had.symm)
  rw [hdf] at hd
  have hd1 : A.val 1 1 = 1 := by
    rcases mul_self_eq_one_iff.mp hd with he | he
    · exact he
    · simpa only [CharTwo.neg_eq] using he
  have ha1 : A.val 0 0 = 1 := by simpa [hd1] using had
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha1, hd1, hb, hc]

/-- The actual Hermitian SL₂ representation is faithful. -/
theorem action_injective (n : ℕ) [NeZero n] : Function.Injective (action n) :=
  (injective_iff_map_eq_one (action n)).mpr (eq_one_of_action_eq_one n)

/-- The given representation, valued in actual linear automorphisms. -/
def linearActionHom (n : ℕ) [NeZero n] :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) →* (Space n ≃ₗ[fixedField n] Space n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (fixedField n) (Space n)).toMonoidHom.comp
    (action n).asGroupHom

@[simp] theorem linearActionHom_apply (n : ℕ) [NeZero n]
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    linearActionHom n A X = action n A X := rfl

theorem linearActionHom_injective (n : ℕ) [NeZero n] :
    Function.Injective (linearActionHom n) := by
  intro A B h
  apply action_injective n
  apply LinearMap.ext
  intro X
  exact congrArg (fun f : Space n ≃ₗ[fixedField n] Space n => f X) h

/-- The matrix-action image as a subgroup of the linear automorphism group. -/
def actionImage (n : ℕ) [NeZero n] : Subgroup (Space n ≃ₗ[fixedField n] Space n) :=
  (linearActionHom n).range

/-- Membership means acting by one of the specified determinant-one matrices. -/
theorem mem_actionImage_iff (n : ℕ) [NeZero n] (g : Space n ≃ₗ[fixedField n] Space n) :
    g ∈ actionImage n ↔ ∃ A : Matrix.SpecialLinearGroup (Fin 2) (Field n),
      ∀ X : Space n, g X = action n A X := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, fun _ => rfl⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, LinearEquiv.ext (fun X => (hA X).symm)⟩

/-- Faithfulness identifies SL₂ with its concrete Hermitian action image. -/
def sl2EquivActionImage (n : ℕ) [NeZero n] :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) ≃* actionImage n :=
  MonoidHom.ofInjective (linearActionHom_injective n)

@[simp] theorem sl2EquivActionImage_coe (n : ℕ) [NeZero n]
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) :
    (sl2EquivActionImage n A).val = linearActionHom n A :=
  MonoidHom.ofInjective_apply _

/-- Compatibility with the image subgroup's natural action. -/
@[simp] theorem sl2EquivActionImage_smul (n : ℕ) [NeZero n]
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    sl2EquivActionImage n A • X = action n A X := by
  change (sl2EquivActionImage n A).val X = _
  rw [sl2EquivActionImage_coe, linearActionHom_apply]

/-- The image equivalence acts by the original matrix congruence formula. -/
theorem sl2EquivActionImage_smul_val (n : ℕ) [NeZero n]
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    (sl2EquivActionImage n A • X).val =
      A.val * X.val * adjoint (conjugation n) A.val := by
  rw [sl2EquivActionImage_smul, action_apply]

theorem actionImage_preserves_form (n : ℕ) [NeZero n] (g : actionImage n) (X : Space n) :
    form n (g • X) = form n X := by
  obtain ⟨A, hA⟩ := g.property
  change form n (g.val X) = _
  rw [← hA, linearActionHom_apply]
  exact form_preserved n A X

/-- In characteristic two the scalar center of SL₂ is trivial. -/
theorem sl2_center_eq_bot (n : ℕ) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (Field n)) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro A hA
  obtain ⟨r, hr, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa only [Fintype.card_fin] using hr
  have hr1 : r = 1 := by
    rcases sq_eq_one_iff.mp hr2 with he | he
    · exact he
    · simpa only [CharTwo.neg_eq] using he
  apply Subtype.ext
  rw [← hs, hr1]
  simp

/-- The canonical quotient map from SL₂ to PSL₂ is an equivalence. -/
def sl2EquivPSL2 (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) (Field n))))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', sl2_center_eq_bot]),
        QuotientGroup.mk'_surjective _⟩

@[simp] theorem sl2EquivPSL2_apply (n : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) :
    sl2EquivPSL2 n A = QuotientGroup.mk A := rfl

/-- PSL₂ is the same concrete Hermitian action image, also for `n = 1`. -/
def psl2EquivActionImage (n : ℕ) [NeZero n] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n) ≃* actionImage n :=
  (sl2EquivPSL2 n).symm.trans (sl2EquivActionImage n)

@[simp] theorem psl2EquivActionImage_mk (n : ℕ) [NeZero n]
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) :
    psl2EquivActionImage n (QuotientGroup.mk A) = sl2EquivActionImage n A := by
  change sl2EquivActionImage n ((sl2EquivPSL2 n).symm (QuotientGroup.mk A)) = _
  rw [← sl2EquivPSL2_apply n A, MulEquiv.symm_apply_apply]

@[simp] theorem psl2EquivActionImage_mk_smul (n : ℕ) [NeZero n]
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    psl2EquivActionImage n (QuotientGroup.mk A) • X = action n A X := by
  rw [psl2EquivActionImage_mk, sl2EquivActionImage_smul]

end Representation.OrthogonalFourMinus.FiniteModel
