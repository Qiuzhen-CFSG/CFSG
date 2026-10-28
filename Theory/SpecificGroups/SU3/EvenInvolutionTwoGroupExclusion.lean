module
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.SU3.BinaryInvolutionTable
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# No two-group involution centralizer in binary PSU₃

Every involution is conjugate to a long-root element. In these coordinates,
the norm-one torus contains a nonidentity projective element of odd order
which centralizes the original root involution. This excludes a two-group
centralizer. A Hermitian basis change transports the result to arbitrary
stored forms, preserving the actual involution and centralizer.

Source: Aschbacher--Smith G.4.1, printed p.342, and Huppert II.10.12.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup
variable {E : Type*} [Field E] [Finite E] [CharP E 2]

/-- The odd norm-one torus excludes two-group centralizers in standard coordinates. -/
theorem standard_involution_centralizer_not_twoGroup
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ¬ IsPGroup 2 (centralizer ({x} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨g,z,_,he,_,_⟩ := BinaryInvolutionTable.involution_root_geometry J hJ hn hcard hfixed x hx
  intro hp
  have hp' := hp.of_equiv (Matrix.SU3.InnerThreeRank.centralizerEquiv (MulAut.conj g) x)
  rw [he] at hp'
  have hq : 2 < 2^n := by
    change 2^1 < 2^n
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨k,hkpow,_,hkne,hkconj⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J (2^n) hcard hfixed hJ hq
  have hzsq : (hermitianUnipotentPSU J hJ z)^2=1 := by
    have hxpow : x^2=1 := hx ▸ pow_orderOf_eq_one x
    rw [←he, ←map_pow, hxpow, map_one]
  let t : centralizer ({hermitianUnipotentPSU J hJ z} : Set _) :=
    ⟨hermitianTorusPSU J hJ k, mem_centralizer_singleton_iff.mpr
      (hermitianTorusPSU_commute_unipotent_of_sq_eq_one J hJ k hkconj z hzsq)⟩
  have htne : t≠1 := fun hh => hkne (congrArg Subtype.val hh)
  have ht2 : 2 ∣ orderOf t := hp'.dvd_orderOf htne
  have htodd : orderOf t ∣ 2^n+1 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    change (hermitianTorusPSU J hJ k) ^ (2^n+1) = 1
    rw [←map_pow, show k^(2^n+1)=1 from Units.ext (by simpa using hkpow), map_one]
  have ho : Odd (2^n+1) := (even_two.pow_of_ne_zero (by omega : n≠0)).add_odd odd_one
  exact ho.not_two_dvd_nat (ht2.trans htodd)

/-- The exclusion holds for the literal projective carrier of any Hermitian form. -/
theorem involution_centralizer_not_twoGroup
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ¬ IsPGroup 2 (centralizer ({x} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hfixed
  intro hp
  exact standard_involution_centralizer_not_twoGroup
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hn hcard hfixed
    (e x) ((e.orderOf_eq x).trans hx) (hp.of_equiv (Matrix.SU3.InnerThreeRank.centralizerEquiv e x))
end BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup
