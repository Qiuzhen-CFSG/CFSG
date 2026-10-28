module
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# Prime rank of the projective degree-three split torus

The change of coordinates (a,b) ↦ (a/b,b³) kills exactly the cubic diagonal
scalars. Thus the actual projective torus is the product of the unit group
and its subgroup of cubes. Counting the cube kernel gives two independent
p-directions whenever p divides the unit order and either p is not three
or nine divides the unit order. In particular the scalar defect is retained
at fields of order four and sixty-four.

The Cartan local-to-global argument uses this in the literal residual Sylow
normalizer, where a zero-core actor bounds the overlap rank by one.
Source: Aschbacher–Smith A.3.18 and 5.2.2, printed pp.51–53,647–649
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3.CartanActions.BorelQuotient
variable (F : Type*) [Field F]

private def torusCoordinates : (Fˣ × Fˣ) →* Fˣ × (powMonoidHom 3 : Fˣ →* Fˣ).range where
  toFun d := (d.1 / d.2, ⟨d.2 ^ 3, d.2, rfl⟩)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_div_mul_comm, mul_pow]

private theorem torusCoordinates_surjective : Function.Surjective (torusCoordinates F) := by
  rintro ⟨a,b,⟨c,rfl⟩⟩
  exact ⟨(a*c,c),by ext <;> simp [torusCoordinates]⟩

private theorem torusCoordinates_ker : (torusCoordinates F).ker = cubicScalars F := by
  ext d
  change (d.1 / d.2, (⟨d.2 ^ 3,d.2,rfl⟩ : (powMonoidHom 3 : Fˣ →* Fˣ).range)) = 1 ↔ _
  simp only [Prod.ext_iff, Prod.fst_one, Prod.snd_one, Subtype.ext_iff]
  change d.1 / d.2 = 1 ∧ d.2 ^ 3 = 1 ↔ d.1 = d.2 ∧ d.1 ^ 3 = 1
  rw [div_eq_one]
  constructor <;> rintro ⟨h,h3⟩ <;> exact ⟨h,by simpa only [h] using h3⟩

/-- The projective torus retains one full unit coordinate and the cubes in the other. -/
def torusCubeCoordinates : ((Fˣ × Fˣ) ⧸ cubicScalars F) ≃*
    Fˣ × (powMonoidHom 3 : Fˣ →* Fˣ).range :=
  (QuotientGroup.quotientMulEquivOfEq (torusCoordinates_ker F).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (torusCoordinates F)
      (torusCoordinates_surjective F))

variable [Finite F] {p : ℕ} [Fact p.Prime]

/-- Two torus directions survive at p, retaining the cubic scalar defect. -/
theorem projective_torus_primeRank_ge_two
    (hd : p ∣ Nat.card F - 1) (hscalar : p ≠ 3 ∨ 9 ∣ Nat.card F - 1) :
    2 ≤ primeRank p ((Fˣ × Fˣ) ⧸ cubicScalars F) := by
  let f := (powMonoidHom 3 : Fˣ →* Fˣ)
  have hcard : Nat.card f.range * Nat.gcd 3 (Nat.card F - 1) = Nat.card F - 1 := by
    rw [←Nat.card_units F]
    have hh := f.ker.card_mul_index
    rw [index_ker,IsCyclic.card_powMonoidHom_ker,Nat.gcd_comm] at hh
    exact (Nat.mul_comm _ _).trans hh
  have hrange : p ∣ Nat.card f.range := by
    rcases hscalar with hp | h9
    · have hc : Nat.Coprime p (Nat.gcd 3 (Nat.card F - 1)) := by
        apply Nat.Coprime.of_dvd_right (Nat.gcd_dvd_left _ _)
        exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
          hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h))
      exact hc.dvd_of_dvd_mul_right (by rwa [hcard])
    · by_cases hp : p = 3
      · subst p
        have h3 : 3 ∣ Nat.card F - 1 := (by decide : 3 ∣ 9).trans h9
        rw [Nat.gcd_eq_left h3] at hcard
        have hh : 3 * 3 ∣ Nat.card f.range * 3 := hcard ▸ h9
        exact Nat.dvd_of_mul_dvd_mul_right (by decide) hh
      · have hc : Nat.Coprime p (Nat.gcd 3 (Nat.card F - 1)) := by
          apply Nat.Coprime.of_dvd_right (Nat.gcd_dvd_left _ _)
          exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
            hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h))
        exact hc.dvd_of_dvd_mul_right (by rwa [hcard])
  have hunit : 1 ≤ primeRank p Fˣ := by
    by_contra hh
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank p Fˣ = 0)
      (by simpa only [Nat.card_units] using hd)
  have hcubes : 1 ≤ primeRank p f.range := by
    by_contra hh
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank p f.range = 0) hrange
  rw [primeRank_equiv p (torusCubeCoordinates F),primeRank_prod_eq_add]
  change 2 ≤ primeRank p Fˣ + primeRank p f.range
  omega
end Matrix.PSL3.CartanActions.BorelQuotient
