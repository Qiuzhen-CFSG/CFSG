module

public import Theory.SpecificGroups.SU3.FullCentralizer
public import Theory.SpecificGroups.SU3.InvolutionEigenbasis
/-!
# Involution conjugacy and full centralizers in SU₃

A unitary matrix conjugating the standard involution to a special unitary
matrix can be corrected to a special unitary conjugator. Multiply its last
column by the inverse determinant: this factor has norm one and commutes
with `diag(-1,-1,1)`. This construction works for any identity-Gram form and
requires no finite-field or cube-root argument.

The full GU₂ centralizer equivalence then transports along a supplied
conjugator, with the determinant-corrected block embedding retained in its
application formula. Over a finite quadratic field of odd characteristic,
the orthonormal eigenbasis theorem supplies the unitary conjugator. Thus all
involutions are conjugate inside the actual SU₃, and every full involution
centralizer is isomorphic to the actual GU₂. Characteristic three is included.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.3.21(a), printed p. 55 (PDF p. 66).
-/

public section

open Matrix
open scoped Matrix
open BenderSuzuki.MatrixGroups
namespace Matrix.SU3
variable {F : Type*} [Field F]

private def correction (J : HermitianForm 3 F) (C : J.unitarySubgroup) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero
    !![1, 0, 0; 0, 1, 0; 0, 0, C.val.val.det⁻¹]
    (by simpa [Matrix.det_fin_three] using inv_ne_zero C.val.det_ne_zero)

private theorem correction_mem (J : HermitianForm 3 F) (hJ : J.form = 1)
    (C : J.unitarySubgroup) : correction J C ∈ J.unitarySubgroup := by
  have hd := unitary_det_norm J hJ C
  have hi : (J.conj C.val.val.det)⁻¹ * C.val.val.det⁻¹ = 1 := by
    rw [← mul_inv, hd, inv_one]
  rw [J.mem_unitarySubgroup_iff, hJ, mul_one]
  change J.conjTranspose !![1, 0, 0; 0, 1, 0; 0, 0, C.val.val.det⁻¹] *
    !![1, 0, 0; 0, 1, 0; 0, 0, C.val.val.det⁻¹] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hi]

private theorem correction_det (J : HermitianForm 3 F) (C : J.unitarySubgroup) :
    GeneralLinearGroup.det (correction J C) = (GeneralLinearGroup.det C.val)⁻¹ := by
  apply Units.ext
  simp [correction, GeneralLinearGroup.val_det_apply, Matrix.det_fin_three]

private theorem correction_commutes (J : HermitianForm 3 F) (hJ : J.form = 1)
    (C : J.unitarySubgroup) :
    correction J C * (standardInvolution J hJ).val =
      (standardInvolution J hJ).val * correction J C := by
  apply Units.ext
  change !![1, 0, 0; 0, 1, 0; 0, 0, C.val.val.det⁻¹] *
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
    !![1, 0, 0; 0, 1, 0; 0, 0, C.val.val.det⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- Correct a unitary conjugator to determinant one without changing its action
on the standard involution. -/
theorem exists_special_conjugator_of_unitary
    (J : HermitianForm 3 F) (hJ : J.form = 1) (A : J.specialSubgroup)
    (C : J.unitarySubgroup)
    (hC : C.val * (standardInvolution J hJ).val * C.val⁻¹ = A.val) :
    ∃ g : J.specialSubgroup, g * standardInvolution J hJ * g⁻¹ = A := by
  let D := correction J C
  have hD : D ∈ J.unitarySubgroup := correction_mem J hJ C
  let g : J.specialSubgroup := ⟨C.val * D, J.unitarySubgroup.mul_mem C.property hD,
    by
      change GeneralLinearGroup.det (C.val * correction J C) = 1
      rw [map_mul, correction_det, mul_inv_cancel]⟩
  refine ⟨g, Subtype.ext ?_⟩
  change (C.val * D) * (standardInvolution J hJ).val * (C.val * D)⁻¹ = A.val
  have he : D * (standardInvolution J hJ).val = (standardInvolution J hJ).val * D :=
    correction_commutes J hJ C
  calc
    _ = C.val * (D * (standardInvolution J hJ).val) * D⁻¹ * C.val⁻¹ := by
      simp only [_root_.mul_inv_rev, mul_assoc]
    _ = C.val * ((standardInvolution J hJ).val * D) * D⁻¹ * C.val⁻¹ := by rw [he]
    _ = A.val := by simpa only [mul_assoc, mul_inv_cancel_left] using hC

/-- A unitary conjugacy to the standard involution already gives conjugacy in SU₃. -/
theorem isConj_standard_of_unitary_conjugator
    (J : HermitianForm 3 F) (hJ : J.form = 1) (A : J.specialSubgroup)
    (C : J.unitarySubgroup)
    (hC : C.val * (standardInvolution J hJ).val * C.val⁻¹ = A.val) :
    IsConj (standardInvolution J hJ) A := by
  obtain ⟨g, hg⟩ := exists_special_conjugator_of_unitary J hJ A C hC
  exact isConj_iff.mpr ⟨g, hg⟩

private def centralizerTransport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({e x} : Set H) where
  toFun y := ⟨e y, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' y z := Subtype.ext (e.map_mul y z)

/-- Transport the full GU₂ centralizer along an actual special unitary conjugator. -/
noncomputable def centralizerEquivOfConjugator
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hchar : (2 : F) ≠ 0) (A g : J3.specialSubgroup)
    (hg : g * standardInvolution J3 h3 * g⁻¹ = A) :
    J2.unitarySubgroup ≃* Subgroup.centralizer ({A} : Set J3.specialSubgroup) :=
  (standardInvolutionCentralizerEquiv J3 J2 h3 h2 hc hchar).trans
    ((centralizerTransport (MulAut.conj g) (standardInvolution J3 h3)).trans
      (MulEquiv.subgroupCongr (congrArg
        (fun x => Subgroup.centralizer ({x} : Set J3.specialSubgroup)) hg)))

theorem centralizerEquivOfConjugator_apply_val
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hchar : (2 : F) ≠ 0) (A g : J3.specialSubgroup)
    (hg : g * standardInvolution J3 h3 * g⁻¹ = A) (B : J2.unitarySubgroup) :
    (centralizerEquivOfConjugator J3 J2 h3 h2 hc hchar A g hg B).val =
      g * blockEmbedding J3 J2 h3 h2 hc B * g⁻¹ := by
  change g * (standardInvolutionCentralizerEquiv J3 J2 h3 h2 hc hchar B).val * g⁻¹ = _
  rw [standardInvolutionCentralizerEquiv_apply_val]

/-- The full centralizer of any matrix conjugate to the standard involution. -/
noncomputable def centralizerEquivOfIsConj
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1) (hc : J3.conj = J2.conj)
    (hchar : (2 : F) ≠ 0) (A : J3.specialSubgroup)
    (hA : IsConj (standardInvolution J3 h3) A) :
    J2.unitarySubgroup ≃* Subgroup.centralizer ({A} : Set J3.specialSubgroup) :=
  centralizerEquivOfConjugator J3 J2 h3 h2 hc hchar A
    (isConj_iff.mp hA).choose (isConj_iff.mp hA).choose_spec

section FiniteField

variable [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- Every involution over the finite quadratic field is conjugate to the standard
involution by an actual special unitary matrix, including in characteristic three. -/
theorem exists_special_involution_conjugator
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (hc : ∀ x, J.conj x = x ^ p)
    (A : J.specialSubgroup) (hA : orderOf A = 2) :
    ∃ g : J.specialSubgroup, g * standardInvolution J hJ * g⁻¹ = A := by
  obtain ⟨C, hC⟩ := exists_unitary_involution_conjugator hp hcard J hJ hc A hA
  exact exists_special_conjugator_of_unitary J hJ A C hC

/-- The standard involution represents every involution conjugacy class in SU₃. -/
theorem isConj_standard_of_orderOf_eq_two
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (hc : ∀ x, J.conj x = x ^ p)
    (A : J.specialSubgroup) (hA : orderOf A = 2) :
    IsConj (standardInvolution J hJ) A :=
  isConj_iff.mpr (exists_special_involution_conjugator hp hcard J hJ hc A hA)

/-- All involutions in the actual SU₃ over the finite quadratic field are conjugate. -/
theorem involutions_isConj
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (hc : ∀ x, J.conj x = x ^ p)
    (A B : J.specialSubgroup) (hA : orderOf A = 2) (hB : orderOf B = 2) :
    IsConj A B :=
  (isConj_standard_of_orderOf_eq_two hp hcard J hJ hc A hA).symm.trans
    (isConj_standard_of_orderOf_eq_two hp hcard J hJ hc B hB)

/-- The full centralizer of any involution in SU₃ over the finite quadratic field
is the actual two-dimensional unitary group. Both forms have identity Gram matrix
and the specified Frobenius conjugation; no recognition hypothesis is used. -/
noncomputable def involutionCentralizerEquiv
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1)
    (hc3 : ∀ x, J3.conj x = x ^ p) (hc2 : ∀ x, J2.conj x = x ^ p)
    (A : J3.specialSubgroup) (hA : orderOf A = 2) :
    J2.unitarySubgroup ≃* Subgroup.centralizer ({A} : Set J3.specialSubgroup) :=
  centralizerEquivOfConjugator J3 J2 h3 h2 (by ext x; rw [hc3, hc2])
    (CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp) A
    (exists_special_involution_conjugator hp hcard J3 h3 hc3 A hA).choose
    (exists_special_involution_conjugator hp hcard J3 h3 hc3 A hA).choose_spec

/-- The full-centralizer equivalence is a conjugate of the determinant-corrected
block embedding, by a special unitary conjugator carrying the standard involution
to the given involution. -/
theorem involutionCentralizerEquiv_eq_conjugated_block
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J3 : HermitianForm 3 F) (J2 : HermitianForm 2 F)
    (h3 : J3.form = 1) (h2 : J2.form = 1)
    (hc3 : ∀ x, J3.conj x = x ^ p) (hc2 : ∀ x, J2.conj x = x ^ p)
    (A : J3.specialSubgroup) (hA : orderOf A = 2) :
    ∃ g : J3.specialSubgroup,
      g * standardInvolution J3 h3 * g⁻¹ = A ∧
      ∀ B : J2.unitarySubgroup,
        (involutionCentralizerEquiv hp hcard J3 J2 h3 h2 hc3 hc2 A hA B).val =
          g * blockEmbedding J3 J2 h3 h2 (by ext x; rw [hc3, hc2]) B * g⁻¹ := by
  refine ⟨(exists_special_involution_conjugator hp hcard J3 h3 hc3 A hA).choose,
    (exists_special_involution_conjugator hp hcard J3 h3 hc3 A hA).choose_spec, ?_⟩
  intro B
  exact centralizerEquivOfConjugator_apply_val J3 J2 h3 h2
    (by ext x; rw [hc3, hc2])
    (CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp) A _ _ B

end FiniteField

end Matrix.SU3

end
