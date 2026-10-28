module
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Moved two-subgroups in binary unitary automorphism groups

The outer group of PSU₃ has a cyclic quotient by its diagonal image, and
each diagonal element has cube one. Thus a two-subgroup R satisfying
[R,Y] = R has trivial outer image: its image in the cyclic quotient is
trivial, and its remaining diagonal image has coprime exponents.
All automorphisms and inner images belong to the actual projective model.

Source: GLS3, Theorem 2.5.12 and §2.7; Aschbacher–Smith, original 4.3.16(2)
and the following elimination, printed p.618. Semilinear coverage is proved
by the imported characteristic-two theorem; no coverage premise remains.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- Commutator movement kills the entire outer image of a two-subgroup. -/
theorem moved_twoGroup_le_inner
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (R Y : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hR : IsPGroup 2 R) (hmoved : ⁅R,Y⁆ = R) :
    R ≤ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let U := ProjectiveSpecialUnitaryMatrixGroup J
  have hcover := semilinear_coverage J hJ hn hc hconj
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  let := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcover
  let q := QuotientGroup.mk' (MulAut.innerSubgroup U)
  let d := QuotientGroup.mk' J.unitaryOuterHom.range
  let f := d.comp q
  have hzero : R.map f = ⊥ := by
    rw [← hmoved,map_commutator]
    apply bot_unique
    have hh : ⁅(⊤ : Subgroup (MulAut.Outer U ⧸ J.unitaryOuterHom.range)),⊤⁆ = ⊥ :=
      commutator_self_eq_bot_iff.mpr inferInstance
    exact (commutator_mono le_top le_top).trans hh.le
  intro r hr
  have hd : q r ∈ J.unitaryOuterHom.range :=
    (QuotientGroup.eq_one_iff _).mp ((Subgroup.map_eq_bot_iff _).mp hzero hr)
  obtain ⟨u,hu⟩ := hd
  have hcube : q r ^ 3 = 1 := by
    rw [← hu]
    obtain ⟨z,hz⟩ := J.unitaryConj_cube_is_inner u
    change q (J.unitaryConjHom u) ^ 3 = 1
    rw [← map_pow,J.unitaryConjHom_apply,hz]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨z,rfl⟩
  have hcop : (orderOf (q r)).Coprime 3 :=
    (hR.orderOf_coprime (by decide : Nat.Coprime 2 3) ⟨r,hr⟩).coprime_dvd_left
      (orderOf_map_dvd (q.comp R.subtype) ⟨r,hr⟩)
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (orderOf_dvd_of_pow_eq_one hcube)))
end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
