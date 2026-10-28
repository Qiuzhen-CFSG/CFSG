module

public import Theory.SpecificGroups.SU3.EvenInvolutionTwoGroupExclusion
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus
public import Theory.NumberTheory.BinarySignedTorus
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Large odd primes in binary PSU₃ involution centralizers

Every involution is conjugate to a long-root element. The genuine projective
norm-one torus centralizes it and has order (q+1)/3 in odd field degree.
The signed-torus calculation gives a prime greater than three. A Hermitian
basis change retains the centralizer of the original involution.

Source: Aschbacher–Smith 14.7.26, printed p.1053, and 16.4.8, p.1188;
Huppert II.10.12 for the root coordinates and torus.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup
variable {E : Type*} [Field E] [Finite E] [CharP E 2]

private theorem standard_large_involution_prime
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 4 ≤ n) (ho : Odd n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      p ∣ Nat.card (centralizer ({x} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨g,z,_,he,_,_⟩ := BinaryInvolutionTable.involution_root_geometry
    J hJ (by omega) hcard hfixed x hx
  have hm : 2^n % 3 = 2 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, if_neg (by
      have := Nat.odd_iff.mp ho
      omega)]
  obtain ⟨_,p,hp,hp3,hd⟩ := Nat.BinarySignedTorus.unitary_quotient (by omega) hm
  refine ⟨p,hp,hp3,?_⟩
  rw [Nat.card_congr (Matrix.SU3.InnerThreeRank.centralizerEquiv (MulAut.conj g) x).toEquiv,he]
  have hzsq : (hermitianUnipotentPSU J hJ z)^2=1 := by
    have hxpow : x^2=1 := hx ▸ pow_orderOf_eq_one x
    rw [←he, ←map_pow, hxpow, map_one]
  have hT : EvenInner.normOneImage J hJ ≤
      centralizer ({hermitianUnipotentPSU J hJ z} : Set _) := by
    rintro _ ⟨k,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (hermitianTorusPSU_commute_unipotent_of_sq_eq_one J hJ k.val k.property z hzsq)
  have hc := card_dvd_of_le hT
  rw [EvenInner.normOneImage_card_binary J hcard
    (huppert_II_10_4_conj_eq_frobenius J (2^n) hcard hfixed) hJ hm] at hc
  exact hd.trans hc

theorem exists_prime_gt_three_dvd_involution_centralizer
    (J : HermitianForm 3 E) {n : ℕ} (hn : 4 ≤ n) (ho : Odd n)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      p ∣ Nat.card (centralizer ({x} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hfixed
  rw [Nat.card_congr (Matrix.SU3.InnerThreeRank.centralizerEquiv e x).toEquiv]
  exact standard_large_involution_prime
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hn ho hcard hfixed
    (e x) ((e.orderOf_eq x).trans hx)

end BenderSuzuki.MatrixGroups.HermitianForm.EvenInvolutionTwoGroup
