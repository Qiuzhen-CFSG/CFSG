module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion.Orders
/-!
# The prime parameter of an odd linear-three cover

The defining prime cube divides the group order, while its scalar factor
has order at most three. If a second defining prime were smaller, its
order polynomial would force the larger prime cube to divide a quadratic
factor smaller than that cube. Thus both SL₃ and PSL₃ determine their prime.

This comparison is consumed by the two-radical normalizer argument in
`Normalizer.lean`, for the actual containing component of an escaping local.
Source: Aschbacher--Smith, proof of 1.3.8, printed p.513.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
open Chapter1.XiEmbedding
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion
variable {Q : Type*} [Group Q]

private theorem defining_cube_dvd {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hm : LinearThreeModel p Q) : p ^ 3 ∣ Nat.card Q := by
  obtain ⟨d,hdpos,hd,he⟩ := linearThree_order hm
  have hc : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr (by
    intro h; have := Nat.le_of_dvd (by omega : 0 < d) h; omega)
  apply (hc.pow_left 3).dvd_of_dvd_mul_right
  rw [he]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

private theorem parameter_le {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq3 : 3 < q) (hoq : Odd q)
    (hm : LinearThreeModel p Q) (hmq : LinearThreeModel q Q) : p ≤ q := by
  by_contra! hlt
  have hop : Odd p := hp.odd_of_ne_two (by omega)
  have hqp : q + 1 < p := by
    obtain ⟨a,ha⟩ := hop
    obtain ⟨b,hb⟩ := hoq
    omega
  obtain ⟨d,_,_,he⟩ := linearThree_order hmq
  have hd : p ^ 3 ∣ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by
    rw [←he]
    exact dvd_mul_of_dvd_left (defining_cube_dvd hp hp3 hm) _
  have hq : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (by
    intro h; have := Nat.le_of_dvd (by omega : 0 < q) h; omega)
  have hqm : Nat.Coprime p (q-1) := hp.coprime_iff_not_dvd.mpr (by
    intro h; have := Nat.le_of_dvd (by omega : 0 < q-1) h; omega)
  have hqa : Nat.Coprime p (q+1) := hp.coprime_iff_not_dvd.mpr (by
    intro h; have := Nat.le_of_dvd (by omega : 0 < q+1) h; omega)
  have hq2 : q^2 - 1 = (q-1)*(q+1) := by
    have h := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have h2 := Nat.sub_add_cancel (by nlinarith : 1 ≤ q^2)
    nlinarith
  have hq3e : q^3 - 1 = (q-1)*(q^2+q+1) := by
    have h := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have h3 := Nat.sub_add_cancel (by nlinarith [sq_nonneg (q:ℤ)] : 1 ≤ q^3)
    nlinarith [sq_nonneg (q:ℤ)]
  rw [hq2,hq3e] at hd
  have hf : q^3 * ((q-1)*(q^2+q+1)) * ((q-1)*(q+1)) =
      (q^3 * (q-1)^2 * (q+1)) * (q^2+q+1) := by ring
  rw [hf] at hd
  have hcop : Nat.Coprime (p^3) (q^3 * (q-1)^2 * (q+1)) :=
    (((hq.pow_right 3).mul_right (hqm.pow_right 2)).mul_right hqa).pow_left 3
  have hdiv : p^3 ∣ q^2+q+1 := hcop.dvd_of_dvd_mul_left hd
  have hle := Nat.le_of_dvd (by positivity : 0 < q^2+q+1) hdiv
  have hsq : q^2+q+1 < p^2 := by nlinarith
  have hpow : p^2 ≤ p^3 := by nlinarith [sq_nonneg (p:ℤ)]
  omega

/-- The prime parameter is intrinsic to either of the two linear-three covers. -/
theorem linearThree_prime_eq {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq3 : 3 < q)
    (hm : LinearThreeModel p Q) (hmq : LinearThreeModel q Q) : p = q :=
  le_antisymm (parameter_le hp hp3 hq3 (hq.odd_of_ne_two (by omega)) hm hmq)
    (parameter_le hq hq3 hp3 (hp.odd_of_ne_two (by omega)) hmq hm)

end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
