module
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiAllActors
public import Theory.SpecificGroups.Suzuki.OddTorusContainment

/-!
# The individual Suzuki involution bound

A primitive prime with binary multiplicative order 4(2m+1) divides the
actual Suzuki group order. Its cyclic subgroup lies in an odd torus.
The torus normalizer has even order, so it contains an involution, which
inverts the torus. The commutator with that involution still has the
primitive prime order. Displacement subadditivity and involution fusion
give at least 2(2m+1) moved dimensions for every involution. The previously
proved order-twenty calculation supplies the parameter-zero endpoint.

Source: DGS85, *Groups and Graphs*, (5.10)(b), pp.110–112, Suzuki branch.
This stronger individual estimate does not require a larger quadratic
actor or a generation assumption. CriticalSupporting applies it to the
original quotient and a specified original involution image.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- Every actual maximal odd Suzuki torus admits an inverting involution. -/
theorem suzuki_torus_inverting_involution {m : ℕ} (hm : 0 < m)
    (U : Subgroup (SuzukiMatrixGroup m)) (hU : IsSuzukiMaximalOddTorus m U) :
    ∃ t : SuzukiMatrixGroup m, orderOf t=2 ∧ ∀ x ∈ U, t*x*t⁻¹=x⁻¹ := by
  have hd : 2 ∣ Nat.card (normalizer (U : Set (SuzukiMatrixGroup m))) := by
    rw [←relIndex_mul_card_of_le (le_normalizer (H := U))]
    rcases hU.normalizer_index hm with h | h <;> rw [h] <;> omega
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (U : Set (SuzukiMatrixGroup m))) 2 hd
  have ht' := (Subgroup.orderOf_coe t).trans ht
  exact ⟨t,ht',hU.involution_inverts hm ht' t.property⟩

/-- Every Suzuki involution moves at least twice the defining field degree.
A primitive odd prime in a torus has binary degree four times that field
degree. An inverting involution bounds its displacement by twice its own. -/
theorem suzuki_involution_field_degree_lower {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (a : SuzukiMatrixGroup m) (ha : orderOf a=2) :
    2*(2*m+1) ≤ fixedCodim ρ (zpowers a) := by
  obtain ⟨p,hp,hpdeg⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
    (n := 2*m+1) ⟨m,rfl⟩ (by omega)
  have hp2 : p≠2 := by
    rintro rfl
    rw [show (2 : ZMod 2)=0 from rfl,orderOf_zero] at hpdeg
    omega
  let : Fact p.Prime := ⟨hp⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := SuzukiMatrixGroup m) p
    (Representation.Suzuki.prime_dvd_card_of_orderOf_two hm hp hpdeg)
  obtain ⟨U,hxU,hU⟩ := suzukiOddSubgroup_exists_torus hm (zpowers x)
    (by simpa only [Nat.card_zpowers,hx] using hpo)
  obtain ⟨t,ht,hi⟩ := suzuki_torus_inverting_involution hm U hU
  have hcomm : t*x*t⁻¹*x⁻¹=x⁻¹^2 := by rw [hi x (hxU (mem_zpowers x)),pow_two]
  have horder : orderOf (t*x*t⁻¹*x⁻¹)=p := by
    have hcop : (orderOf x⁻¹).Coprime 2 := by
      simpa only [orderOf_inv,hx] using hpo.coprime_two_right
    rw [hcomm,hcop.orderOf_pow,orderOf_inv,hx]
  have hl := prime_order_le_fixedCodim ρ hf hp hp2 (t*x*t⁻¹*x⁻¹) horder
  rw [hpdeg] at hl
  have hu := fixedCodim_commutator_le_twice ρ t x
  obtain ⟨g,hg⟩ := isConj_iff.mp (suzuki_involutions_isConj m hm a t ha ht)
  have heq : fixedCodim ρ (zpowers t) = fixedCodim ρ (zpowers a) := by
    rw [←hg,fixedCodim_zpowers_conj]
  rw [heq] at hu
  omega

/-- DGS (5.10)(b), Suzuki branch, including Sz(2). The individual estimate
holds for every involution without assuming a larger quadratic actor. -/
theorem suzuki_element_fixed_index (m : ℕ)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (a : SuzukiMatrixGroup m) (ha : orderOf a=2) :
    2^(2*(2*m+1)) ≤ Nat.card (V ⧸ fixedSpace ρ (zpowers a)) := by
  have hd : 2*(2*m+1) ≤ fixedCodim ρ (zpowers a) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using suzukiZero_involution_fixedCodim_ge_two ρ hf a ha
    · exact suzuki_involution_field_degree_lower hm ρ hf a ha
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hd
end Representation.RankOne.QuadraticRecognition
