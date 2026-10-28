module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeSquare.RootPreimage
public import Theory.GroupTheory.Commutator.ScalarNorm
public import Theory.GroupTheory.PerfectCentralSupplement

/-!
# Defining-prime exclusion for PSU₃(p²)

The root subgroup has order p⁶ and index prime to p. Its full preimage in
a central cover has central first-coordinate kernel, by partial inversion
and generation by centered roots. The units of the fixed field of order
p² act by scalars and fix the covering kernel.

The scalar norm annihilates fixed derived elements by p²−1. Central
transfer puts every central kernel element of order p in this derived
group, a contradiction. This argument includes p = 3 and p = 5.
A genuine Hermitian basis equivalence transports it to the original form,
preserving the literal projective carrier and covering kernel. The last
theorem applies it to the constructed universal projection.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), printed pp.407–408
(PDF pp.418–419), with A.2.2–3; GLS3, Theorem 6.1.4 and Tables 6.1.2–3.
-/

open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.PrimeSquare
open OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
variable {E : Type*} [Group E] (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J))

/-- The standard root subgroup at q = p² has index prime to p. -/
public theorem rootGroup_index_not_dvd {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = (p ^ 2) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p ^ 2) :
    ¬ p ∣ (rootGroup J hJ).index := by
  obtain ⟨_, _, _, _, _, _, _, _, hGcard, _⟩ :=
    huppert_II_10_12 J (p^2) hcard hfixed hJ
  have hgcd : Nat.gcd 3 (p^2 + 1) ∣ (p^2)^2 - 1 := by
    have hf : (p^2)^2 - 1 = (p^2 - 1) * (p^2 + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (p^2) 1
    rw [hf]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (p^2 + 1)) _
  have hdiv : Nat.gcd 3 (p^2 + 1) ∣ ((p^2)^3 + 1) * (p^2)^3 * ((p^2)^2 - 1) :=
    dvd_mul_of_dvd_right hgcd _
  have hi := (rootGroup J hJ).card_mul_index
  rw [rootGroup_card J hJ (p^2) hcard hfixed] at hi
  have hprod : (rootGroup J hJ).index * Nat.gcd 3 (p^2 + 1) =
      ((p^2)^3 + 1) * ((p^2)^2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos hp.pos 2) 3)
    calc
      (p^2)^3 * ((rootGroup J hJ).index * Nat.gcd 3 (p^2 + 1)) =
          Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) * Nat.gcd 3 (p^2 + 1) := by
            rw [← mul_assoc, hi]
      _ = ((p^2)^3 + 1) * (p^2)^3 * ((p^2)^2 - 1) := by
        rw [hGcard, Nat.div_mul_cancel hdiv]
      _ = (p^2)^3 * (((p^2)^3 + 1) * ((p^2)^2 - 1)) := by ring
  intro hbad
  have hd : p ∣ ((p^2)^3 + 1) * ((p^2)^2 - 1) :=
    hprod ▸ dvd_mul_of_dvd_left hbad _
  have hp2 : p ∣ p^2 := dvd_pow_self p (by decide)
  rcases hp.dvd_mul.mp hd with h | h
  · exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_trans hp2
      (dvd_pow_self (p^2) (by decide : 3 ≠ 0)))).mpr h)
  · have hsq : 1 ≤ (p^2)^2 := one_le_pow₀ (one_le_pow₀ hp.one_le)
    have hp4 : p ∣ (p^2)^2 := dvd_trans hp2 (dvd_pow_self (p^2) (by decide))
    rw [← Nat.sub_add_cancel hsq] at hp4
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hp4)

include hJ in
/-- The defining-prime exclusion on the standard form, including p = 3 and 5. -/
public theorem not_defining_prime_dvd_kernel_standard {p : ℕ} [Fact p.Prime] [CharP F p]
    (hodd : p ≠ 2) (hcard : Nat.card F = (p^2)^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p^2) [Finite E] :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  have hp : p.Prime := Fact.out
  have htwo : (2 : F) ≠ 0 := by
    intro hz
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp hz))
  have hKcard : Nat.card (fixedField J) = p^2 := hfixed
  have hK : 4 < Nat.card (fixedField J) := by
    rw [hKcard]
    have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
    nlinarith
  intro hbad
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hbad
  have hzE : orderOf (z : E) = p := (Subgroup.orderOf_coe z).trans hz
  let Z := zpowers (z : E)
  have hZker : Z ≤ f.toMonoidHom.ker := zpowers_le.mpr z.property
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1) (by
    simpa only [Z, Nat.card_zpowers, pow_one] using hzE)
  have hkerH : f.toMonoidHom.ker ≤ rootPreimage J hJ f :=
    (rootGroup J hJ).ker_le_comap f.toMonoidHom
  let zH : rootPreimage J hJ f := ⟨z, hkerH z.property⟩
  have hzder : (z : E) ∈ ⁅rootPreimage J hJ f, rootPreimage J hJ f⁆ := by
    apply central_pSubgroup_le_commutator (rootPreimage J hJ f) Z
      (hZker.trans hkerH) (hZker.trans f.ker_le_center) hZp _ (mem_zpowers _)
    rw [rootPreimage, index_comap_of_surjective _ f.surjective]
    exact rootGroup_index_not_dvd J hJ hp hcard hfixed
  have hzD : zH ∈ _root_.commutator (rootPreimage J hJ f) := by
    rw [← map_subtype_commutator] at hzder
    obtain ⟨y, hy, he⟩ := hzder
    exact (show y = zH from Subtype.ext he) ▸ hy
  have hpow := CentralExtension.ScalarNorm.fixed_derived_pow_card_units hK
    (coordinate J hJ f) (coordinate_surjective J hJ f htwo)
    (coordinate_ker_le_center J hJ f hodd)
    (scalarAction J hJ f) (coordinate_scalarAction J hJ f) zH hzD
    (fun t => scalarAction_kernel J hJ f t zH z.property)
  have he : (z : E) ^ (p^2 - 1) = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Nat.card_units, hKcard] using
      congrArg Subtype.val hpow
  have hd : p ∣ p^2 - 1 := by
    have h := orderOf_dvd_of_pow_eq_one he
    rwa [hzE] at h
  have hp2 : p ∣ p^2 := dvd_pow_self p (by decide)
  rw [← Nat.sub_add_cancel (one_le_pow₀ hp.one_le : 1 ≤ p^2)] at hp2
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right hd).mpr hp2)

/-- The defining prime is absent from every finite perfect-cover kernel at q = p². -/
public theorem not_defining_prime_dvd_kernel {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hcard : Nat.card F = (p^2)^2)
    (hconj : ∀ x, J.conj x = x^(p^2)) [Finite E] :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (f := 4)
    (by simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hfixed := card_fixed J hcard hconj
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (p^2) hcard hfixed
  let g : PerfectCentralCovering.Cover E
      (ProjectiveSpecialUnitaryMatrixGroup
        (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)) := {
    toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
    surjective := e.surjective.comp f.surjective
    isPerfect := f.isPerfect
    ker_le_center := by
      intro x hx
      exact f.ker_le_center (e.injective (hx.trans e.map_one.symm)) }
  have hk : g.toMonoidHom.ker = f.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  rw [← hk]
  exact not_defining_prime_dvd_kernel_standard
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl g hodd hcard hfixed

/-- Application to the actual constructed universal projection. -/
public theorem not_defining_prime_dvd_universal_kernel {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hcard : Nat.card F = (p^2)^2)
    (hconj : ∀ x, J.conj x = x^(p^2)) :
    ¬ p ∣ Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hp2 : 2 < p^2 := by nlinarith [hp.two_le]
  let := projective_isQuasisimple J hp2 hcard hconj
  exact not_defining_prime_dvd_kernel J
    (PerfectCentralCovering.universalCover (ProjectiveSpecialUnitaryMatrixGroup J))
    hp hodd hcard hconj

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.PrimeSquare
