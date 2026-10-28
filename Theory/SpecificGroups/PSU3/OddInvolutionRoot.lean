module
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeField
import all Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeField
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Inner.Conjugacy
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.TorusPreservation
/-!
# Defining-characteristic roots inverted by odd PSU₃ involutions

A centered Hermitian root has order p and is inverted by the sign torus.
The projective involution-conjugacy theorem and a Hermitian basis change
transport this root to any actual projective involution. The internal import
reuses the existing centered-root equations without widening their API.

Source: Aschbacher–Smith E.2.17, printed p.230.
-/
public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionRoot
open OddPrimeSylow.NormalizedOuter.Coverage
open UniversalCover.OddKernelBound
variable {F : Type*} [Field F]
private theorem standard_root {p : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (h2 : (2:F)≠0) :
    ∃ r : ProjectiveSpecialUnitaryMatrixGroup J, orderOf r = p ∧
      hermitianTorusPSU J hJ (-1) * r * (hermitianTorusPSU J hJ (-1))⁻¹ = r⁻¹ := by
  let r := root J hJ (centered J 1)
  have hr : orderOf r = p := by
    apply orderOf_eq_prime
    · change root J hJ (centered J 1) ^ p = 1
      rw [← map_pow, centered_prime_pow, map_one]
    · intro h
      have he : centered J 1 = 1 := (root_injective J hJ) (h.trans (map_one _).symm)
      have hh := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) he
      apply h2
      change (2:F)*1=0 at hh
      simpa using hh
  refine ⟨r,hr,?_⟩
  change hermitianTorusPSU J hJ (-1) * root J hJ (centered J 1) *
    (hermitianTorusPSU J hJ (-1))⁻¹ = (root J hJ (centered J 1))⁻¹
  rw [hermitianTorusPSU_mul_unipotent,mul_inv_cancel_right,centered_inverted,map_inv]

theorem exists_inverted_root [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp2 : p≠2)
    (hF : Nat.card F = p^2) (hc : ∀ x, J.conj x = x^p)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    ∃ r : ProjectiveSpecialUnitaryMatrixGroup J, orderOf r = p ∧ t*r*t⁻¹=r⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have h2 : (2:F)≠0 := by
    intro hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp hz))
  have hfixed : Nat.card {x:F // J.conj x=x}=p := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1
      (by decide) (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hc)
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J p hF hfixed
  let J' := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let z := hermitianTorusPSU J' rfl (-1)
  obtain ⟨r,hr,hzr⟩ := standard_root J' rfl h2
  have hz : orderOf z = 2 := torus_neg_orderOf J' rfl h2
  have he : IsConj z (e t) := InvolutionConjugateBounds.Inner.projective_involutions_isConj
    J' hp hp2 hF hc z (e t) hz ((e.orderOf_eq t).trans ht)
  obtain ⟨g,hg⟩ := isConj_iff.mp he
  let f := (MulAut.conj g).trans e.symm
  have hfz : f z = t := by
    change e.symm (g*z*g⁻¹)=t
    rw [hg,e.symm_apply_apply]
  refine ⟨f r,(f.orderOf_eq r).trans hr,?_⟩
  rw [←hfz,←map_inv,←map_mul,←map_mul]
  calc
    f (z*r*z⁻¹) = f r⁻¹ := congrArg f hzr
    _ = (f r)⁻¹ := map_inv f r
end BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionRoot
