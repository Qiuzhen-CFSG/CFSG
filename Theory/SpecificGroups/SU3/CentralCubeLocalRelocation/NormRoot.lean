module

public import Theory.SpecificGroups.SU3.CentralCubeLocalRelocation.ScalarRoot
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus

/-!
# The norm-one cube root forced by the original SU₃ matrix

The special-to-projective kernel identifies the given central element with
its actual scalar u. The determinant-one cubic matrix argument produces a
cube root a of u in the ground field. Since u has order three, a has order
nine. Its order divides q²−1, and q=2ⁿ with n odd gives gcd(9,q−1)=1.
Thus 9 divides q+1 and a has norm one for the original stored involution.

Source: the central cube step in Aschbacher--Smith A.2.12(II), p.37.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.EvenInner
namespace BenderSuzuki.MatrixGroups.HermitianForm.CentralCubeLocalRelocation
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
/-- An element of order nine in the quadratic field has norm one when the
binary degree is odd. -/
theorem ninth_root_norm_one (J : HermitianForm 3 F) {n : ℕ} (hn : Odd n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (a : Fˣ) (ha : orderOf a = 9) :
    a ∈ normOne J := by
  have hq : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hn
    rw [pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hp : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
  have hcop3 : Nat.Coprime 3 (2 ^ n - 1) := by
    apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    intro hd
    have he := Nat.mod_eq_zero_of_dvd hd
    omega
  have hcop9 : Nat.Coprime 9 (2 ^ n - 1) := hcop3.pow_left 2
  have hd : 9 ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
    have he := orderOf_dvd_natCard a
    rw [ha, Nat.card_units, hcard] at he
    rwa [show (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1] at he
  have hdiv : 9 ∣ 2 ^ n + 1 := hcop9.dvd_of_dvd_mul_left hd
  rw [normOne_eq_rootsOfUnity J hconj, mem_rootsOfUnity]
  exact orderOf_dvd_iff_pow_eq_one.mp (ha ▸ hdiv)

/-- The original central cube equation produces a norm-one scalar of order
nine, retaining the exact scalar matrix of the given central element. -/
theorem exists_norm_one_cube_root (J : HermitianForm 3 F) {n : ℕ}
    (hn : 3 ≤ n) (ho : Odd n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ a, J.conj a = a ^ (2 ^ n)) (z : J.specialSubgroup)
    (hz : z ∈ center J.specialSubgroup) (hz1 : z ≠ 1)
    (x : J.specialSubgroup) (hx : x ^ 3 = z) :
    ∃ a : normOne J, orderOf a = 9 ∧
      z.val = GeneralLinearGroup.scalar (Fin 3) (a.val ^ 3) := by
  have hk := J.specialToProjective_ker_eq_center
    (EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj)
  have hzk : z ∈ J.specialToProjective.ker := hk.symm ▸ hz
  have hGL : z.val ∈ center (GL (Fin 3) F) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hzk)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hGL
  obtain ⟨u, hu⟩ := hGL
  have hu3 : u ^ 3 = 1 :=
    ((UniversalCover.scalar_mem_special_iff J u).mp (hu ▸ z.property)).2
  have hu1 : u ≠ 1 := by
    intro he
    apply hz1
    apply Subtype.ext
    rw [← hu, he, map_one]
    rfl
  have hdet : x.val.val.det = 1 := congrArg Units.val x.property.2
  have hc : x.val.val ^ 3 = Matrix.scalar (Fin 3) (u : F) := by
    have he := congrArg (fun y : J.specialSubgroup => y.val.val) hx
    exact he.trans (congrArg Units.val hu).symm
  obtain ⟨a, ha⟩ := Matrix.exists_cube_root_of_det_one_cube_scalar x.val.val hdet u hc
  have ha0 : a ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide)] at ha
    exact u.ne_zero ha.symm
  let au : Fˣ := Units.mk0 a ha0
  have ha3 : au ^ 3 = u := Units.ext ha
  have ha9 : au ^ 9 = 1 := by
    rw [show 9 = 3 * 3 from rfl, pow_mul, ha3, hu3]
  have haorder : orderOf au = 9 :=
    orderOf_eq_prime_pow (p := 3) (n := 1) (by simpa [ha3] using hu1) ha9
  let b : normOne J := ⟨au, ninth_root_norm_one J ho hcard hconj au haorder⟩
  exact ⟨b, (Subgroup.orderOf_mk _ _).trans haorder, by rw [ha3]; exact hu.symm⟩

end BenderSuzuki.MatrixGroups.HermitianForm.CentralCubeLocalRelocation
