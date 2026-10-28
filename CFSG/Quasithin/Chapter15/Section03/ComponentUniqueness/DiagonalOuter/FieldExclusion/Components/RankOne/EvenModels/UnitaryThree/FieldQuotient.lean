module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal

/-!
# Trivial diagonal contribution in the rank-one unitary branch

A unitary conjugation has outer order dividing both three and q + 1.
Thus it is inner when q is one modulo three. Under explicit semilinear
coverage, the existing cyclic field-image argument then makes the actual
outer automorphism group cyclic. It requires neither uniqueness of field
parameters nor faithfulness of their action.

Source: GLS3, Theorem 2.5.12(c,d,f) and the unitary matrix description in
Section 2.7; Aschbacher--Smith, proof of 15.3.38, printed p.1137.
-/

public section
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.UnitaryThree
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The determinant kills the diagonal quotient when the fixed-field order is one modulo three. -/
theorem unitary_inner (q : ℕ) (hmod : q % 3 = 1)
    (hconj : ∀ x, J.conj x = x ^ q) (u : J.unitarySubgroup) :
    J.unitaryConj u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let I := MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)
  let π := QuotientGroup.mk' I
  have hc : π (J.unitaryConj u) ^ 3 = 1 := by
    obtain ⟨b, hb⟩ := J.unitaryConj_cube_is_inner u
    rw [← map_pow, hb]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
  have hd : u.val.val.det ^ (q + 1) = 1 := by
    simpa only [hconj, pow_succ] using J.unitary_det_norm_one u
  let v : J.specialSubgroup := ⟨u.val ^ (q + 1), by
    refine ⟨J.unitarySubgroup.pow_mem u.property _, ?_⟩
    apply Units.ext
    simpa using hd⟩
  have he : (J.unitaryConj u) ^ (q + 1) = MulAut.conj (J.specialToProjective v) := by
    rw [← J.unitaryConjHom_apply, ← map_pow J.unitaryConjHom, J.unitaryConjHom_apply]
    exact J.unitaryConj_special_is_inner v
  have hp : π (J.unitaryConj u) ^ (q + 1) = 1 := by
    rw [← map_pow, he]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
  have hg : Nat.gcd 3 (q + 1) = 1 := by
    rw [Nat.gcd_rec, show (q + 1) % 3 = 2 by omega]
    decide
  have ho : orderOf (π (J.unitaryConj u)) ∣ 1 := by
    rw [← hg]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc) (orderOf_dvd_of_pow_eq_one hp)
  exact (QuotientGroup.eq_one_iff _).mp ((orderOf_eq_one_iff).mp (Nat.eq_one_of_dvd_one ho))

/-- Semilinear coverage makes the actual outer group cyclic when every unitary
conjugation is inner. The field image need not be faithful. -/
theorem outer_cyclic [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hi : ∀ u : J.unitarySubgroup,
      J.unitaryConj u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hcov : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcov
  let := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcov
  apply isCyclic_of_injective (QuotientGroup.mk' J.unitaryOuterHom.range)
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  apply bot_unique
  rintro _ ⟨u, rfl⟩
  apply Subgroup.mem_bot.mpr
  change QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (J.unitaryConjHom u) = 1
  rw [J.unitaryConjHom_apply]
  exact (QuotientGroup.eq_one_iff _).mpr (hi u)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne.UnitaryThree
