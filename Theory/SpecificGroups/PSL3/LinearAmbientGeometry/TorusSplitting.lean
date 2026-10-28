module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.TorusControl
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# Splitting the linear Borel by its full torus

The full diagonal torus acts separately on all three upper-unitriangular
coordinates. For a finite field of even order greater than two, its normalizer
intersects the unipotent radical trivially. The torus is an odd Hall subgroup
of the Borel. These facts supply a complement in the original source Sylow
via the normal-Sylow Frattini argument, including field four.

Source: Aschbacher--Smith, §5.3.2 and §5.3.7; the matrix calculations use the
standard diagonal action in PSL₃.
-/

public noncomputable section
open Subgroup Subgroup.OddHall Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.CartanActions Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

def diagonalScale (d : Fˣ × Fˣ) (u : U F) : U F :=
  ⟨(d.1 * (d.1*d.2) : Fˣ) * u.x,
    ((d.1*d.2)⁻¹*d.2⁻¹ : Fˣ) * u.y, (d.1*d.2⁻¹ : Fˣ) * u.c⟩

omit [Finite F] in
theorem diagonal_conj (d : Fˣ × Fˣ) (u : U F) :
    torusMap F d * projective F u * (torusMap F d)⁻¹ =
      projective F (diagonalScale F d u) := by
  change projection F (torusSL F d) * projection F (specialLinear F u) *
    (projection F (torusSL F d))⁻¹ = projection F (specialLinear F _)
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg (projection F)
  rw [←map_inv]
  apply Subtype.ext
  change (torusSL F d).val * matrix F u * (torusSL F d⁻¹).val = matrix F _
  rw [torusSL_val,torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,diagonalScale,Matrix.diagonal_mul,Matrix.mul_diagonal,
      mul_assoc,mul_left_comm,mul_comm]
  all_goals field_simp

theorem unipotent_torus_normalizer_trivial
    {n : ℕ} (hF : Nat.card F = 2^n) (hq : 2 < Nat.card F)
    (u : PSL(3,F)) (hu : u ∈ unipotent F)
    (hn : u ∈ normalizer (torus F : Set PSL(3,F))) : u=1 := by
  have hdis : Disjoint (unipotent F) (torus F) := by
    have hc : Nat.Coprime (Nat.card (unipotent F)) (Nat.card (torus F)) := by
      rw [card_unipotent,hF,←pow_mul]
      have ht : Odd (Nat.card (torus F)) := by
        apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd (torusMap F))
        rw [Nat.card_prod]
        exact (BorelQuotient.units_odd F hF).mul (BorelQuotient.units_odd F hF)
      exact ht.coprime_two_left.pow_left _
    exact disjoint_of_coprime_natCard hc
  have hc (t : PSL(3,F)) (ht : t ∈ torus F) : t*u=u*t := by
    have hxD : u*t*u⁻¹*t⁻¹ ∈ torus F := (torus F).mul_mem
      ((mem_normalizer_iff.mp hn t).mp ht) ((torus F).inv_mem ht)
    have hxU : u*t*u⁻¹*t⁻¹ ∈ unipotent F := by
      have hnU := borel_le_normalizer_unipotent F (torus_le_borel F ht)
      have hh := (unipotent F).mul_mem hu
        ((mem_normalizer_iff.mp hnU u⁻¹).mp ((unipotent F).inv_mem hu))
      simpa only [mul_assoc] using hh
    have hx := disjoint_def.mp hdis hxU hxD
    have he : u*t=t*u := by
      calc
        u*t = (u*t*u⁻¹*t⁻¹)*(t*u) := by group
        _ = t*u := by rw [hx,one_mul]
    exact he.symm
  rw [←projective_range F] at hu
  obtain ⟨v,rfl⟩ := hu
  have he (d : Fˣ × Fˣ) : diagonalScale F d v=v := by
    apply projective_injective F
    rw [←diagonal_conj]
    rw [hc _ ⟨d,rfl⟩,mul_inv_cancel_right]
  have hunit : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hunit
  obtain ⟨a,ha⟩ := exists_ne (1:Fˣ)
  have ha' : (a:F) ≠ 1 := fun hh => ha (Units.ext hh)
  have hai : ((a⁻¹:Fˣ):F) ≠ 1 := fun hh => (inv_ne_one.mpr ha) (Units.ext hh)
  have hx := congrArg U.x (he (1,a))
  have hy := congrArg U.y (he (a,1))
  have hz := congrArg U.c (he (a,1))
  have hv : v=1 := by
    apply U.ext
    · exact eq_zero_of_mul_eq_self_left ha' (by simpa [diagonalScale] using hx)
    · exact eq_zero_of_mul_eq_self_left hai (by simpa [diagonalScale] using hy)
    · exact eq_zero_of_mul_eq_self_left ha' (by simpa [diagonalScale] using hz)
  rw [hv,map_one]

theorem torus_oddHall {n : ℕ} (hF : Nat.card F = 2^n) :
    IsHallSubgroup oddPrimes ((torus F).subgroupOf (borel F)) := by
  have ht : Odd (Nat.card (torus F)) := by
    apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd (torusMap F))
    rw [Nat.card_prod]
    exact (BorelQuotient.units_odd F hF).mul (BorelQuotient.units_odd F hF)
  constructor
  · intro p hp he
    have hcard := Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv
    have hd : 2 ∣ Nat.card (torus F) := by rwa [hcard,show p.val=2 from he] at hp
    exact ht.not_two_dvd_nat hd
  · intro p hp he
    rw [(BorelQuotient.borel_complement F hF).index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
      card_unipotent,hF,←pow_mul] at hp
    exact he (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hp)

end Matrix.PSL3.LinearAmbientGeometry
