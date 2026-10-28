module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FieldParameters
public import Theory.SpecificGroups.SU3.UnitaryEight.Reduction
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus

/-!
# Scalar correction for cubic triangular unitary actions

The faithful projective action turns a cubic automorphism into a scalar
matrix cube. For an upper triangular unitary matrix, its middle diagonal
entry has norm one. Dividing the determinant by the cube of that entry
therefore gives a norm-one element of exponent dividing three. If nine
divides the order of the cyclic norm-one group, this element has a cube
root in that same group. Scaling the matrix gives determinant one without
changing its projective action.

Source: the unitary exclusion in Aschbacher--Smith, 15.3.37, printed p.1135.
The scalar-correction method also occurs in the checked calculation
`Theory/SpecificGroups/SU3/UnitaryEight/MatrixCentralizer.lean`; here it is
proved for arbitrary even field orders with nine dividing q + 1.
-/

open Matrix BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal.BorelCubic

private theorem cube_root_of_nine_dvd {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hcard : 9 ∣ Nat.card G) (x : G) (hx : x ^ 3 = 1) : ∃ y : G, y ^ 3 = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr (hg x)
  change g ^ m = x at hm
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hd : Nat.card G ∣ m * 3 := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_mul, hm]
    exact hx
  have hm3 : 3 ∣ m := by
    have := hcard.trans hd
    omega
  obtain ⟨k, rfl⟩ := hm3
  exact ⟨g ^ k, by rw [← pow_mul, Nat.mul_comm k 3, hm]⟩

variable {F : Type*} [Field F] [Finite F]

/-- A cubic projective upper triangular unitary matrix is special projectively
when the norm-one group has order divisible by nine. -/
public theorem triangular_projective_cubic_is_inner
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (h9 : 9 ∣ 2 ^ n + 1) (u : J.unitarySubgroup)
    (h10 : u.val.val 1 0 = 0) (h20 : u.val.val 2 0 = 0)
    (h21 : u.val.val 2 1 = 0) (hu : (J.unitaryConjHom u) ^ 3 = 1) :
    J.unitaryConjHom u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP F 2 := charP_two n hn hcard
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n ≤ 1 := by omega
    interval_cases n
    norm_num at h9
  have hc : ∃ t : F, J.conj t ≠ t := by
    by_contra h
    push Not at h
    exact J.conj_ne_one_of_card n hn2 hcard (fixed_card J n hn hcard hconj)
      (RingEquiv.ext h)
  have hp : (ProjGenLinGroup.mk u.val) ^ 3 = 1 :=
    UnitaryEight.projective_pow_eq_one J hJ hc u 3
      (by simpa only [J.unitaryConjHom_apply] using hu)
  have hs : u.val ^ 3 ∈ Subgroup.center (GL (Fin 3) F) :=
    ProjGenLinGroup.mk_eq_one.mp (by simpa only [map_pow] using hp)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨c, hc3⟩ := hs
  have hunit := (J.mem_unitarySubgroup_iff _).mp u.property
  rw [hJ] at hunit
  have hb1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 1 1) hunit
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
    h21] at hb1
  let b : Fˣ := Units.mk0 (u.val.val 1 1) (right_ne_zero_of_mul_eq_one hb1)
  have hb : b ∈ EvenInner.normOne J := eq_inv_of_mul_eq_one_left hb1
  have hb3 : c = b ^ 3 := by
    apply Units.ext
    have he := congrArg (fun A : GL (Fin 3) F => A.val 1 1) hc3
    simpa [GeneralLinearGroup.coe_scalar, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_three, h10, h20, h21, b] using he
  have hdet3 : (GeneralLinearGroup.det u.val) ^ 3 = b ^ 9 := by
    have he := congrArg GeneralLinearGroup.det hc3.symm
    simpa only [map_pow, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      hb3, ← pow_mul] using he
  let D : EvenInner.normOne J := ⟨GeneralLinearGroup.det u.val,
    eq_inv_of_mul_eq_one_left (J.unitary_det_norm_one u)⟩
  let B : EvenInner.normOne J := ⟨b, hb⟩
  have hd : (D * (B ^ 3)⁻¹) ^ 3 = 1 := by
    apply Subtype.ext
    change ((GeneralLinearGroup.det u.val) * (b ^ 3)⁻¹) ^ 3 = 1
    rw [mul_pow, hdet3, inv_pow, ← pow_mul]
    exact mul_inv_cancel _
  obtain ⟨a, ha⟩ := cube_root_of_nine_dvd
    (by rwa [EvenInner.normOne_card J hcard hconj]) (D * (B ^ 3)⁻¹) hd
  have hab : (a * B) ^ 3 = D := by rw [mul_pow, ha]; group
  let t : Fˣ := (a * B).val
  have ht : t ^ 3 = GeneralLinearGroup.det u.val := congrArg Subtype.val hab
  have htnorm : J.conj ((t⁻¹ : Fˣ) : F) * ((t⁻¹ : Fˣ) : F) = 1 := by
    have hm := (EvenInner.normOne J).inv_mem (a * B).property
    change J.conj ((t⁻¹ : Fˣ) : F) = (((t⁻¹ : Fˣ) : F))⁻¹ at hm
    rw [hm, inv_mul_cancel₀ (Units.ne_zero _)]
  let w : J.specialSubgroup :=
    ⟨GeneralLinearGroup.scalar (Fin 3) t⁻¹ * u.val,
      J.unitarySubgroup.mul_mem (J.scalar_mem_unitary_of_norm_one t⁻¹ htnorm) u.property,
      by
        change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) t⁻¹ * u.val) = 1
        simp [map_mul, GeneralLinearGroup.det_scalar, ← ht]⟩
  refine ⟨J.specialToProjective w, ?_⟩
  rw [J.unitaryConjHom_apply, ← J.unitaryConj_special_is_inner]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp [J.unitaryConj_apply_val, w, map_mul]

end CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal.BorelCubic
