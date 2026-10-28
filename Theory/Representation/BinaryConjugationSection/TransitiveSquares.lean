module

public import Theory.Representation.BinaryConjugationSection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Squares over a transitive binary quotient

Suppose P/E carries a conjugation action transitive on its nonzero vectors.
If E/U is central in P/U and has exponent two, a single square-one lift
outside E forces every element of P/U to have square one. The proof compares
an arbitrary element with a conjugate of the chosen lift and computes their
squares in the literal quotient P/U. No linear structure on P/U is assumed.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.73(3), printed pp.1076–1077. The root spaces supply the square-one
lift and the natural SL₂(4) action supplies transitivity.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H P E : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}

/-- A central binary kernel and one square-one lift make the original quotient elementary. -/
theorem elementary_quotient_of_transitive
    (d : BinaryConjugationSection H P E ρ) (U : Subgroup G)
    [(U.subgroupOf P).Normal]
    (hNU : H ≤ normalizer U) (hcomm : ⁅P, E⁆ ≤ U)
    (hEsq : ∀ e ∈ E, e ^ 2 ∈ U)
    (hseed : ∃ p : P, (p : G) ^ 2 ∈ U ∧ d.coordinates p ≠ 1)
    (htrans : ∀ u v : W, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v) :
    IsElementaryAbelian 2 (P ⧸ U.subgroupOf P) := by
  let q := QuotientGroup.mk' (U.subgroupOf P)
  have hq (p : P) : q p = 1 ↔ (p : G) ∈ U := QuotientGroup.eq_one_iff p
  obtain ⟨v, hvsq, hv⟩ := hseed
  have hsquare (a : P) : q a ^ 2 = 1 := by
    by_cases ha : d.coordinates a = 1
    · rw [← map_pow]
      exact (hq _).mpr (hEsq a ((d.coordinates_eq_one_iff a).mp ha))
    obtain ⟨h, hh⟩ := htrans _ _ hv ha
    let b : P := ⟨h * v * (h : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized h.property) v).mp v.property⟩
    have hcoord : d.coordinates b = d.coordinates a :=
      Multiplicative.toAdd.injective ((d.equivariant h v).trans hh)
    have hbsq : q b ^ 2 = 1 := by
      rw [← map_pow]
      apply (hq _).mpr
      change (MulAut.conj (h : G) (v : G)) ^ 2 ∈ U
      rw [← map_pow]
      exact (mem_normalizer_iff.mp (hNU h.property) _).mp hvsq
    let c : P := b⁻¹ * a
    have hc : (c : G) ∈ E := by
      apply (d.coordinates_eq_one_iff c).mp
      change d.coordinates (b⁻¹ * a) = 1
      rw [map_mul, map_inv, hcoord, inv_mul_cancel]
    have hcsq : q c ^ 2 = 1 := by
      rw [← map_pow]
      exact (hq _).mpr (hEsq c hc)
    have hbc : Commute (q b) (q c) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (hq _).mpr (hcomm (commutator_mem_commutator b.property hc))
    calc
      q a ^ 2 = (q b * q c) ^ 2 := by simp [c]
      _ = q b ^ 2 * q c ^ 2 := hbc.mul_pow 2
      _ = 1 := by rw [hbsq, hcsq, mul_one]
  have hall (x : P ⧸ U.subgroupOf P) : x ^ 2 = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) x
    exact hsquare a
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hall x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall }

end Representation.BinaryConjugationSection
