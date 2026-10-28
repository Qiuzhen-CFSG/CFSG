module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Residual
public import Mathlib.GroupTheory.Sylow

/-!
# The binary Hermitian root subgroup is Sylow

The actual projective root image has order `q³`. Huppert II.10.12 gives
its ambient projective group order, including the scalar divisor
`gcd(3,q+1)`. Multiplying the root index by this divisor gives
`(q³+1)(q²-1)`, which is odd when `q = 2ⁿ` and `n > 0`. Thus the root
image is a Sylow two-subgroup.

This is the defining-characteristic Sylow calculation used in the PSU₃
case of Aschbacher (1975), Lemma 3.4, p.96. The index argument adapts
`Coverage.RootSylow.rootGroup_index_not_dvd` from prime fixed-field order
to binary prime-power fixed-field order.
-/

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity.UnitarySylow
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem root_index_odd {n : ℕ} (hn : n ≠ 0)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) :
    ¬ 2 ∣ (rootImage J hJ).index := by
  obtain ⟨_, _, _, _, _, _, _, _, hGcard, _⟩ :=
    huppert_II_10_12 J (2^n) hcard hfixed hJ
  have hgcd : Nat.gcd 3 (2^n + 1) ∣ (2^n)^2 - 1 := by
    rw [show (2^n)^2 - 1 = (2^n - 1) * (2^n + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq (2^n) 1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (2^n + 1)) _
  have hdiv : Nat.gcd 3 (2^n + 1) ∣ ((2^n)^3 + 1) * (2^n)^3 * ((2^n)^2 - 1) :=
    dvd_mul_of_dvd_right hgcd _
  have hi := (rootImage J hJ).card_mul_index
  rw [rootImage_card J hJ hcard hfixed] at hi
  have hprod : (rootImage J hJ).index * Nat.gcd 3 (2^n + 1) =
      ((2^n)^3 + 1) * ((2^n)^2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2^n)^3)
    calc
      (2^n)^3 * ((rootImage J hJ).index * Nat.gcd 3 (2^n + 1)) =
          Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) * Nat.gcd 3 (2^n + 1) := by
            rw [← mul_assoc, hi]
      _ = ((2^n)^3 + 1) * (2^n)^3 * ((2^n)^2 - 1) := by
        rw [hGcard, Nat.div_mul_cancel hdiv]
      _ = (2^n)^3 * (((2^n)^3 + 1) * ((2^n)^2 - 1)) := by ring
  intro hbad
  have hd : 2 ∣ ((2^n)^3 + 1) * ((2^n)^2 - 1) :=
    hprod ▸ dvd_mul_of_dvd_left hbad _
  have hq : 2 ∣ 2^n := dvd_pow_self 2 hn
  rcases Nat.prime_two.dvd_mul.mp hd with h | h
  · have hp : 2 ∣ (2^n)^3 := hq.trans (dvd_pow_self _ (by decide : 3 ≠ 0))
    have := (Nat.dvd_add_iff_right hp).mpr h
    norm_num at this
  · have hsq : 1 ≤ (2^n)^2 := one_le_pow₀ (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)))
    have hp : 2 ∣ (2^n)^2 := hq.trans (dvd_pow_self _ (by decide : 2 ≠ 0))
    rw [← Nat.sub_add_cancel hsq] at hp
    have := (Nat.dvd_add_iff_right h).mpr hp
    norm_num at this

/-- The explicit projective Hermitian root image as a Sylow two-subgroup. -/
@[expose] public def rootSylow {n : ℕ} (hn : n ≠ 0)
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) :
    Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (rootImage_isTwoGroup J hJ hcard hfixed).toSylow (by exact root_index_odd J hJ hn hcard hfixed)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity.UnitarySylow
