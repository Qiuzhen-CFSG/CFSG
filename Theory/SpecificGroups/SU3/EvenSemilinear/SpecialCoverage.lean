module
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.Coordinates
public import Theory.GroupTheory.PerfectCentralCoverSylowRigidity

/-!
# Semilinear coverage on the actual binary SU₃ matrices

For fixed-field order greater than two, SU₃ is perfect and its projective
kernel is its center. An automorphism descends through that kernel. The
known projective semilinear formula gives a second homomorphism on SU₃ with
the same projection. Uniqueness of maps from a perfect group through a
central extension identifies them, giving equality of GL representatives.
This explicitly eliminates a possible central discrepancy in the lift.

Source: GLS3, Theorem 2.5.12 and §2.7; the special-unitary case of
Aschbacher–Smith F.1.3(5), printed p.260.
-/

public section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open BorelTorus.SemilinearActors
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

include hJ in
private theorem field_special_mem (σ : E ≃+* E) (x : J.specialSubgroup) :
    GeneralLinearGroup.map σ.toRingHom x.val ∈ J.specialSubgroup := by
  obtain ⟨hx, hd⟩ := (J.mem_specialSubgroup_iff x.val).mp x.property
  apply (J.mem_specialSubgroup_iff _).mpr
  constructor
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M.map σ) hx
    have ht : (J.conjTranspose x.val.val).map σ =
        J.conjTranspose (x.val.val.map σ) := by
      ext i j
      exact field_conj_commute J σ _
    have hf : J.form.map σ = J.form := by
      rw [hJ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    change J.conjTranspose (x.val.val.map σ) * J.form * x.val.val.map σ = J.form
    simpa only [Matrix.map_mul, ht, hf] using h
  · apply Units.ext
    change (σ.mapMatrix x.val.val).det = 1
    rw [← RingEquiv.map_det]
    have hd' : x.val.val.det = 1 := congrArg Units.val hd
    rw [hd', map_one]

private def specialSemilinearMap (σ : E ≃+* E) (u : J.unitarySubgroup) :
    J.specialSubgroup →* J.specialSubgroup where
  toFun x := J.specialUnitaryConj u
    ⟨GeneralLinearGroup.map σ.toRingHom x.val, field_special_mem J hJ σ x⟩
  map_one' := by apply Subtype.ext; simp [specialUnitaryConj_val]
  map_mul' x y := by apply Subtype.ext; simp [specialUnitaryConj_val, map_mul, mul_assoc]

include hJ in
/-- Every automorphism of binary SU₃ for n ≥ 2 has a semilinear formula
on actual matrices. No simplicity, coverage, or lifting premise remains. -/
theorem special_semilinear_coverage {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2) (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (a : MulAut J.specialSubgroup) :
    ∃ σ : E ≃+* E, J.HasSpecialUnitarySemilinearForm a σ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ n) hq hcard hfixed
  let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
  let := J.special_isPerfect_of_fixed_card hq hcard hfixed
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  let f : PerfectCentralCovering.Cover J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toMonoidHom := J.specialToProjective
      surjective := J.specialToProjective_surjective
      isPerfect := inferInstance
      ker_le_center := J.specialToProjective_ker_le_center }
  obtain ⟨b, hb⟩ := f.exists_descended_aut (J.specialToProjective_ker_eq_center hz) a
  obtain ⟨σ, u, hu⟩ := semilinear_coverage J hJ hn hcard hconj b
  have he : a.toMonoidHom = specialSemilinearMap J hJ σ u := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      J.specialToProjective J.specialToProjective_ker_le_center
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    have hx := congrArg Subtype.val (hb x)
    change (b (J.specialToProjective x)).val = (J.specialToProjective (a x)).val at hx
    rw [hu] at hx
    simp only [specialToProjective_apply_val] at hx
    simp only [MonoidHom.comp_apply, specialToProjective_apply_val]
    change ProjGenLinGroup.mk (a x).val = ProjGenLinGroup.mk
      (J.specialUnitaryConj u ⟨GeneralLinearGroup.map σ.toRingHom x.val, _⟩).val
    rw [specialUnitaryConj_val]
    rw [← hx, ProjGenLinGroup.map_mk, map_mul, map_mul, map_inv]
  refine ⟨σ,u, fun x => ?_⟩
  simpa only [specialSemilinearMap, MonoidHom.coe_mk, OneHom.coe_mk,
    specialUnitaryConj_val, MulEquiv.coe_toMonoidHom] using congrArg Subtype.val (DFunLike.congr_fun he x)

end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
