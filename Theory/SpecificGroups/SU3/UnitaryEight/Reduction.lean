module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.ScalarKernel
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Outer cubic centralizers in the actual projective unitary group

For the antidiagonal ternary Hermitian form in characteristic two, the scalar
centralizer theorem makes unitary conjugation faithful modulo projective
scalars. Thus innerness and power relations on its automorphism image transfer
to the actual PSU subgroup of PGL. A commuting semilinear formula gives the
corresponding conjugacy equation on those same projective matrices.

Hermitian field conjugation inverts the diagonal outer image. That image is
abelian of exponent three, so a unitary matrix projectively conjugate to its
Hermitian conjugate induces an inner automorphism. This excludes the field
involution from centralizers of outer diagonal cubic actions.

For matrix-field order 64 and fixed-field order 8, the final conditional theorem
uses Cauchy's theorem to reduce oddness of the full automorphism centralizer
to `LinearCentralizerBound`. Arbitrary-automorphism semilinear coverage and
faithfulness of the field component are separate explicit premises. Neither
these two premises nor the linear matrix bound is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 16.4.8,
printed p.1188; GLS3, Theorem 2.5.12 and Section 2.7 for the concrete unitary
and projective automorphism conventions.
-/

public section

open BenderSuzuki.MatrixGroups Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEight
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Equal conjugations on PSU determine the same projective matrix. -/
theorem projective_eq_of_conjugations_eq [CharP E 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hconj : ∃ t : E, J.conj t ≠ t)
    (A B : GL (Fin 3) E)
    (h : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      ProjGenLinGroup.mk A * x.val * (ProjGenLinGroup.mk A)⁻¹ =
        ProjGenLinGroup.mk B * x.val * (ProjGenLinGroup.mk B)⁻¹) :
    ProjGenLinGroup.mk A = ProjGenLinGroup.mk B := by
  have hc : ProjGenLinGroup.mk (B⁻¹ * A) = 1 := by
    apply ProjGenLinGroup.mk_eq_one.mpr
    apply J.projective_centralizer_scalar hJ hconj
    intro x
    apply (mul_inv_eq_iff_eq_mul).mp
    simpa only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_inv, inv_mul_cancel, mul_one] using
      congrArg (fun z => (ProjGenLinGroup.mk B)⁻¹ * z * ProjGenLinGroup.mk B) (h x)
  exact ((inv_mul_eq_one).1 (by simpa only [map_mul, map_inv] using hc)).symm

/-- The action on PSU has precisely the projective scalar ambiguity. -/
theorem unitaryConj_eq_iff_projective_eq [CharP E 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hconj : ∃ t : E, J.conj t ≠ t) (u v : J.unitarySubgroup) :
    J.unitaryConj u = J.unitaryConj v ↔
      ProjGenLinGroup.mk u.val = ProjGenLinGroup.mk v.val := by
  constructor
  · intro h
    apply projective_eq_of_conjugations_eq J hJ hconj
    intro x
    simpa only [J.unitaryConj_apply_val] using
      congrArg (fun a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => (a x).val) h
  · intro h
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [J.unitaryConj_apply_val, h]

/-- Innerness is membership of the same matrix class in the actual PSU image. -/
theorem unitaryConj_mem_inner_iff [CharP E 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hconj : ∃ t : E, J.conj t ≠ t) (u : J.unitarySubgroup) :
    J.unitaryConj u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ↔
      ProjGenLinGroup.mk u.val ∈ ProjectiveSpecialUnitaryMatrixGroup J := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := J.specialToProjective_surjective x
    have hv := (unitaryConj_eq_iff_projective_eq J hJ hconj
      (⟨v.val, v.property.1⟩ : J.unitarySubgroup) u).1
      ((J.unitaryConj_special_is_inner v).trans hx)
    rw [← hv]
    simpa only [J.specialToProjective_apply_val] using (J.specialToProjective v).property
  · rintro ⟨v, hv, hvu⟩
    let x : J.specialSubgroup := ⟨v, hv⟩
    refine ⟨J.specialToProjective x, ?_⟩
    rw [← J.unitaryConj_special_is_inner]
    exact (unitaryConj_eq_iff_projective_eq J hJ hconj _ u).2 hvu

/-- Trivial powers of the action are trivial powers of the actual matrix class. -/
theorem projective_pow_eq_one [CharP E 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hconj : ∃ t : E, J.conj t ≠ t) (u : J.unitarySubgroup)
    (n : ℕ) (hu : (J.unitaryConj u)^n = 1) :
    (ProjGenLinGroup.mk u.val)^n = 1 := by
  have h : J.unitaryConj (u^n) = J.unitaryConj 1 := by
    simpa only [← J.unitaryConjHom_apply, map_pow, map_one] using hu
  have hp := (unitaryConj_eq_iff_projective_eq J hJ hconj (u^n) 1).1 h
  simpa using hp

/-- A commuting semilinear action conjugates the unitary matrix to itself in PGL. -/
theorem projective_conjugate_eq_of_semilinear_commute [CharP E 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hconj : ∃ t : E, J.conj t ≠ t)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u v : J.unitarySubgroup)
    (ha : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk v.val *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk v.val)⁻¹)
    (hcomm : Commute a (J.unitaryConj u)) :
    ProjGenLinGroup.mk (v.val * GeneralLinearGroup.map σ.toRingHom u.val * v.val⁻¹) =
      ProjGenLinGroup.mk u.val := by
  apply projective_eq_of_conjugations_eq J hJ hconj
  intro x
  obtain ⟨y, rfl⟩ := a.surjective x
  have h := congrArg (fun b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) =>
    (b y).val) hcomm.eq
  change (a (J.unitaryConj u y)).val = (J.unitaryConj u (a y)).val at h
  rw [ha, J.unitaryConj_apply_val, J.unitaryConj_apply_val, ha,
    map_mul, map_mul, map_inv, ProjGenLinGroup.map_mk] at h
  rw [ha]
  simpa only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel_left, mul_inv_cancel_right] using h

/-- Field conjugation preserves the actual unitary group of a fixed Gram matrix. -/
def conjugateUnitary
    (hJ : J.form.map J.conj = J.form) (u : J.unitarySubgroup) : J.unitarySubgroup := by
  refine ⟨GeneralLinearGroup.map J.conj.toRingHom u.val, ?_⟩
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val.val.map J.conj) * J.form *
    (u.val.val.map J.conj) = J.form
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A.map J.conj)
    ((J.mem_unitarySubgroup_iff u.val).mp u.property)
  have hadj : (J.conjTranspose u.val.val).map J.conj =
      J.conjTranspose (u.val.val.map J.conj) := by
    ext i j
    rfl
  simpa only [RingEquiv.mapMatrix_apply, Matrix.map_mul, hadj, hJ] using h

/-- The unitary field-conjugation lift uses entrywise conjugation of matrices. -/
@[simp] theorem conjugateUnitary_val
    (hJ : J.form.map J.conj = J.form) (u : J.unitarySubgroup) :
    (conjugateUnitary J hJ u).val = GeneralLinearGroup.map J.conj.toRingHom u.val := by rfl

/-- Hermitian conjugation inverts the actual diagonal outer image. -/
theorem unitaryOuter_conjugate (hJ : J.form.map J.conj = J.form)
    (u : J.unitarySubgroup) :
    J.unitaryOuterHom (conjugateUnitary J hJ u) = (J.unitaryOuterHom u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul]
  let x : J.specialSubgroup := ⟨(u * conjugateUnitary J hJ u).val,
    (u * conjugateUnitary J hJ u).property, by
      apply Units.ext
      change (u.val.val * u.val.val.map J.conj).det = 1
      rw [Matrix.det_mul, show (u.val.val.map J.conj).det = J.conj u.val.val.det from
        (J.conj.map_det _).symm]
      simpa only [mul_comm] using J.unitary_det_norm_one u⟩
  change QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (J.unitaryConjHom (u * conjugateUnitary J hJ u)) = 1
  rw [J.unitaryConjHom_apply]
  apply (QuotientGroup.eq_one_iff _).2
  exact ⟨J.specialToProjective x, (J.unitaryConj_special_is_inner x).symm⟩

/-- A unitary class conjugate to its Hermitian conjugate is already in PSU. -/
theorem inner_of_conjugate_projective_eq [Finite E]
    (hJ : J.form.map J.conj = J.form) (u v : J.unitarySubgroup)
    (h : ProjGenLinGroup.mk
      (v.val * GeneralLinearGroup.map J.conj.toRingHom u.val * v.val⁻¹) =
        ProjGenLinGroup.mk u.val) :
    J.unitaryConj u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let w := conjugateUnitary J hJ u
  have ha : J.unitaryConj (v * w * v⁻¹) = J.unitaryConj u := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [J.unitaryConj_apply_val]
    change ProjGenLinGroup.mk
      (v.val * GeneralLinearGroup.map J.conj.toRingHom u.val * v.val⁻¹) * x.val * _ = _
    change ProjGenLinGroup.mk
      (v.val * GeneralLinearGroup.map J.conj.toRingHom u.val * v.val⁻¹) * x.val *
      (ProjGenLinGroup.mk
        (v.val * GeneralLinearGroup.map J.conj.toRingHom u.val * v.val⁻¹))⁻¹ = _
    rw [h]
  let := J.unitaryOuterHom_range_isCyclic
  let := IsCyclic.commGroup (α := J.unitaryOuterHom.range)
  have hc : Commute (J.unitaryOuterHom v) (J.unitaryOuterHom w) := by
    exact congrArg Subtype.val (Commute.all
      (⟨J.unitaryOuterHom v, ⟨v, rfl⟩⟩ : J.unitaryOuterHom.range)
      (⟨J.unitaryOuterHom w, ⟨w, rfl⟩⟩ : J.unitaryOuterHom.range)).eq
  have he : J.unitaryOuterHom u = J.unitaryOuterHom w := by
    have ho := congrArg
      (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))) ha
    simp only [← J.unitaryConjHom_apply] at ho
    change J.unitaryOuterHom (v * w * v⁻¹) = J.unitaryOuterHom u at ho
    rw [map_mul, map_mul, map_inv, hc.eq, mul_assoc, mul_inv_cancel, mul_one] at ho
    exact ho.symm
  have hsquare : (J.unitaryOuterHom u)^2 = 1 := by
    have hinv := unitaryOuter_conjugate J hJ u
    change J.unitaryOuterHom w = _ at hinv
    rw [← he] at hinv
    calc
      (J.unitaryOuterHom u)^2 = J.unitaryOuterHom u * (J.unitaryOuterHom u)⁻¹ := by
        rw [pow_two, ← hinv]
      _ = 1 := mul_inv_cancel _
  have hcube : (J.unitaryOuterHom u)^3 = 1 := by
    obtain ⟨x, hx⟩ := J.unitaryConj_cube_is_inner u
    change (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (J.unitaryConjHom u))^3 = 1
    rw [← map_pow, J.unitaryConjHom_apply]
    exact (QuotientGroup.eq_one_iff _).2 ⟨x, hx.symm⟩
  have hone : J.unitaryOuterHom u = 1 := by
    simpa only [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hsquare, one_mul] using hcube
  change QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (J.unitaryConjHom u) = 1 at hone
  rw [J.unitaryConjHom_apply] at hone
  exact (QuotientGroup.eq_one_iff _).1 hone


/-- The remaining linear matrix calculation: an outer projective cubic
has no nonidentity projective unitary involution in its centralizer. -/
@[expose] def LinearCentralizerBound : Prop :=
  ∀ u v : J.unitarySubgroup,
    (ProjGenLinGroup.mk u.val)^3 = 1 →
    ProjGenLinGroup.mk u.val ∉ ProjectiveSpecialUnitaryMatrixGroup J →
    (ProjGenLinGroup.mk v.val)^2 = 1 →
    Commute (ProjGenLinGroup.mk v.val) (ProjGenLinGroup.mk u.val) →
    ProjGenLinGroup.mk v.val = 1

/-- Conditional assembly for the actual PSU₃(8). The three premises isolate
coverage, field faithfulness, and a purely projective matrix calculation. -/
theorem odd_centralizer_of_matrix_bound [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = 64)
    (hfixed : Nat.card {z : E // J.conj z = z} = 8)
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    (hfaithful : ∀ σ : E ≃+* E, J.HasUnitarySemilinearForm 1 σ → σ = 1)
    (hlinear : LinearCentralizerBound J)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ∈ J.unitaryConjHom.range) (ha3 : orderOf a = 3)
    (houter : a ∉ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Odd (Nat.card (Subgroup.centralizer ({a} : Set (MulAut
      (ProjectiveSpecialUnitaryMatrixGroup J))))) := by
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 6) (by
    simpa only [← Nat.card_eq_fintype_card, show (2:ℕ)^6 = 64 from rfl] using hcard)
  have hconj : ∃ t : E, J.conj t ≠ t := by
    by_contra h
    push Not at h
    apply J.conj_ne_one_of_card 3 (by decide) (by simpa only [show ((2:ℕ)^3)^2 = 64 from rfl] using hcard)
      (by simpa only [show (2:ℕ)^3 = 8 from rfl] using hfixed)
    exact RingEquiv.ext h
  have hform : J.form.map J.conj = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Finite.of_injective
      (fun b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) =>
        (b : ProjectiveSpecialUnitaryMatrixGroup J → ProjectiveSpecialUnitaryMatrixGroup J))
      DFunLike.coe_injective
  obtain ⟨u, rfl⟩ := ha
  simp only [J.unitaryConjHom_apply] at ha3 houter ⊢
  have hu3 : (J.unitaryConj u)^3 = 1 := by
    simpa only [ha3] using pow_orderOf_eq_one (J.unitaryConj u)
  have huP : ProjGenLinGroup.mk u.val ∉ ProjectiveSpecialUnitaryMatrixGroup J :=
    fun h => houter ((unitaryConj_mem_inner_iff J hJ hconj u).2 h)
  apply Nat.not_even_iff_odd.mp
  intro heven
  let C := Subgroup.centralizer ({J.unitaryConj u} :
    Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp heven)
  have htorder : orderOf t.val = 2 :=
    (orderOf_injective C.subtype C.subtype_injective t).trans ht
  obtain ⟨ht2, htne⟩ := orderOf_eq_prime_iff.mp htorder
  have htcomm : Commute t.val (J.unitaryConj u) :=
    Subgroup.mem_centralizer_singleton_iff.mp t.property
  obtain ⟨σ, hσ⟩ := hcoverage t.val
  have hσ2 : σ^2 = 1 := by
    apply hfaithful
    simpa only [← pow_two, ht2] using hσ.mul J hJ hσ
  by_cases hσ1 : σ = 1
  · rw [hσ1] at hσ
    obtain ⟨v, hv⟩ := (HasUnitarySemilinearForm.one_iff J).1 hσ
    have hv2 : (J.unitaryConj v)^2 = 1 := hv ▸ ht2
    have hvcomm : Commute (J.unitaryConj v) (J.unitaryConj u) := hv ▸ htcomm
    have hvu : J.unitaryConj (v*u) = J.unitaryConj (u*v) := by
      simpa only [← J.unitaryConjHom_apply, map_mul] using hvcomm.eq
    have hpcomm : Commute (ProjGenLinGroup.mk v.val) (ProjGenLinGroup.mk u.val) := by
      change _ * _ = _ * _
      simpa only [Subgroup.coe_mul, map_mul] using
        (unitaryConj_eq_iff_projective_eq J hJ hconj (v*u) (u*v)).1 hvu
    have hpv := hlinear u v (projective_pow_eq_one J hJ hconj u 3 hu3) huP
      (projective_pow_eq_one J hJ hconj v 2 hv2) hpcomm
    apply htne
    rw [hv]
    have hv1 := (unitaryConj_eq_iff_projective_eq J hJ hconj v 1).2
      (by simpa only [Subgroup.coe_one, map_one] using hpv)
    simpa only [← J.unitaryConjHom_apply, map_one] using hv1
  · have hσJ := J.field_involution_eq_conj 3 (by decide)
      (by simpa only [show ((2:ℕ)^3)^2 = 64 from rfl] using hcard) (by simpa only [show (2:ℕ)^3 = 8 from rfl] using hfixed) σ hσ2 hσ1
    obtain ⟨v, hv⟩ := hσ
    have hp := projective_conjugate_eq_of_semilinear_commute J hJ hconj
      t.val σ u v hv htcomm
    rw [hσJ] at hp
    exact houter (inner_of_conjugate_projective_eq J hform u v hp)

end BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEight
