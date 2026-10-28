module
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Setup
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
import all Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence

/-!
# Field transport preserving the marked outer involution

An isomorphism of coefficient fields preserving the Gram matrix and Hermitian
involution maps special-unitary representatives entrywise and descends to
PSU. The inverse coefficient map supplies its inverse. Applying this formula
to representatives shows that it intertwines the prescribed entrywise actions.
Finite fields of order 25 are isomorphic, and fifth powers commute with that
isomorphism; the antidiagonal Gram matrix has prime-field entries.

The deliberate implementation import of `FiniteFieldEquivalence` extends its
coefficient equivalence by a projective representative formula. This avoids
changing that shared module; no private names occur in the exported types.
The projective map is the actual map on PGL, retaining the scalar kernel.

This is the field-independence step for the S₇ calculation in Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, manuscript pp.10–11.
-/

open Matrix
public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
variable {E F : Type*} [Field E] [Field F]

private def coefficientHom (e : E ≃+* F) (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form) :
    ProjectiveSpecialUnitaryMatrixGroup J →* ProjectiveSpecialUnitaryMatrixGroup K :=
  ((ProjGenLinGroup.map e.toRingHom).comp
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype).codRestrict _ (by
      intro x
      obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
      refine ⟨(coefficientSpecialEquiv e J K hc hf u).val,
        (coefficientSpecialEquiv e J K hc hf u).property, ?_⟩
      change ProjGenLinGroup.mk _ = ProjGenLinGroup.map e.toRingHom (J.specialToProjective u).val
      rw [specialToProjective_apply_val, ProjGenLinGroup.map_mk]
      rfl)

private theorem coefficientHom_mk (e : E ≃+* F) (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form)
    (u : J.specialSubgroup) :
    coefficientHom e J K hc hf (J.specialToProjective u) =
      K.specialToProjective (coefficientSpecialEquiv e J K hc hf u) := by
  apply Subtype.ext
  change ProjGenLinGroup.map e.toRingHom (J.specialToProjective u).val = _
  rw [specialToProjective_apply_val, ProjGenLinGroup.map_mk, specialToProjective_apply_val]
  rfl

/-- Coefficient transport on the actual projective images. -/
def coefficientEquiv (e : E ≃+* F) (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup K := by
  have hc' (x : F) : e.symm (K.conj x) = J.conj (e.symm x) := by
    apply e.injective
    simpa only [e.apply_symm_apply] using (hc (e.symm x)).symm
  have hf' : K.form.map e.symm = J.form := by
    rw [← hf]
    ext i j
    exact e.symm_apply_apply _
  exact
    { coefficientHom e J K hc hf with
      invFun := coefficientHom e.symm K J hc' hf'
      left_inv := by
        intro x
        apply Subtype.ext
        change ProjGenLinGroup.map e.symm.toRingHom (ProjGenLinGroup.map e.toRingHom x.val) = x.val
        rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp]
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        change ProjGenLinGroup.map e.toRingHom (ProjGenLinGroup.map e.symm.toRingHom x.val) = x.val
        rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp]
        simp }

@[simp] theorem coefficientEquiv_mk (e : E ≃+* F) (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form)
    (u : J.specialSubgroup) :
    coefficientEquiv e J K hc hf (J.specialToProjective u) =
      K.specialToProjective (coefficientSpecialEquiv e J K hc hf u) := by
  apply Subtype.ext
  change ProjGenLinGroup.map e.toRingHom (J.specialToProjective u).val = _
  rw [specialToProjective_apply_val, ProjGenLinGroup.map_mk, specialToProjective_apply_val]
  rfl

/-- Coefficient transport intertwines the specified entrywise actions. -/
theorem coefficientEquiv_entrywise (e : E ≃+* F) (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : J.IsEntrywiseConjugation a) :
    K.IsEntrywiseConjugation (MulAut.congr (coefficientEquiv e J K hc hf) a) := by
  intro u
  obtain ⟨x, rfl⟩ := (coefficientSpecialEquiv e J K hc hf).surjective u
  obtain ⟨y, hy, hya⟩ := ha x
  refine ⟨coefficientSpecialEquiv e J K hc hf y, ?_, ?_⟩
  · change y.val.val.map e = (x.val.val.map e).map K.conj
    rw [hy]
    ext i j
    exact hc _
  · rw [← coefficientEquiv_mk]
    change coefficientEquiv e J K hc hf
      (a ((coefficientEquiv e J K hc hf).symm
        (coefficientEquiv e J K hc hf (J.specialToProjective x)))) = _
    rw [MulEquiv.symm_apply_apply, hya, coefficientEquiv_mk]

/-- Every field of order 25 gives the same marked antidiagonal projective model. -/
theorem exists_marked_equiv [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = 5 ^ 2) (hc : ∀ x, J.conj x = x ^ 5)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : J.IsEntrywiseConjugation a) :
    ∃ e : ProjectiveSpecialUnitaryMatrixGroup J ≃* ConcreteGroup,
      MulAut.congr e a = concreteActor := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype E := Fintype.ofFinite E
  let : Fintype (GaloisField 5 (2 * 1)) := Fintype.ofFinite _
  let e : E ≃+* GaloisField 5 (2 * 1) := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
    exact (GaloisField.card 5 (2 * 1) (by decide)).symm)
  have hec (x : E) : e (J.conj x) = concreteForm.conj (e x) := by
    rw [hc, concreteForm_conj, map_pow]
  have hef : J.form.map e = concreteForm.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [concreteForm, OddPrimeSylow.NormalizedOuter.FormTransport.standardForm]
  refine ⟨coefficientEquiv e J concreteForm hec hef, ?_⟩
  exact IsEntrywiseConjugation.unique concreteForm
    (coefficientEquiv_entrywise e J concreteForm hec hef a ha) concreteActor_entrywise

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
