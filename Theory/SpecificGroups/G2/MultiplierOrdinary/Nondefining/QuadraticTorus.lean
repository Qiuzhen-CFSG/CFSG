module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.ShortBlock
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.NormOne
public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Quadratic nonsplit primes in even-characteristic G₂

The two norm-one tori of the actual quadratic extension embed through commuting
short- and long-root SL₂ factors in the split-octonion automorphism group.
Their product has order (q+1)². Frobenius in the first factor inverts it and
fixes the second factor. For a prime r>3 dividing q+1, the exact G₂ order
makes the torus index prime to r, so it contains a full Sylow r-subgroup.
Independent inversion kills the central commutator pairing; Sylow transfer
then excludes r from the literal universal covering kernel.

This proves the quadratic nonsplit branch of Aschbacher–Smith I.1.3–I.1.4,
printed pp.407–408 (PDF pp.418–419), citing GLS3 §6.1. The other nondefining
branches and the defining-prime calculation remain with their own consumers.
The octonion model and order theorem are the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section

open Matrix Subgroup PerfectCentralCovering
open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining

namespace Atlas.G2.MultiplierOrdinary.Nondefining
namespace QuadraticTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem exists_nonsplit_product :
    ∃ (ι : normOne F × normOne F →* Model F) (w : Model F),
      Function.Injective ι ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ c, w * ι (1,c) * w⁻¹ = ι (1,c)) := by
  obtain ⟨s, v, hs, hv⟩ := exists_normOne_SL (F := F)
  let ι := pairHom.comp (s.prodMap s)
  refine ⟨ι, pairHom (v,1),
    pairHom_injective.comp (Prod.map_injective.mpr ⟨hs, hs⟩), ?_, ?_⟩
  · intro c
    change pairHom (v,1) * pairHom (s c,s 1) *
      (pairHom (v,1))⁻¹ = pairHom (s c⁻¹,s 1)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg pairHom
    apply Prod.ext
    · exact hv c
    · simp
  · intro c
    change pairHom (v,1) * pairHom (s 1,s c) *
      (pairHom (v,1))⁻¹ = pairHom (s 1,s c)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg pairHom
    apply Prod.ext <;> simp

theorem product_index (ι : normOne F × normOne F →* Model F)
    (hι : Function.Injective ι) :
    ι.range.index = Nat.card F ^ 6 * (Nat.card F - 1)^2 *
      (Nat.card F^4 + Nat.card F^2 + 1) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hf2 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
  have hf6 : Nat.card F ^ 6 - 1 =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 + Nat.card F ^ 2 + 1) := by
    simpa [Finset.sum_range_succ, ← pow_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
      (geom_sum_mul_of_one_le (Nat.one_le_pow 2 (Nat.card F) hq.le) 3).symm
  have hcardT : Nat.card ι.range = (Nat.card F + 1)^2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv,
      Nat.card_prod, card_normOne, pow_two]
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.succ_pos (Nat.card F)) 2)
  rw [← hcardT, Subgroup.card_mul_index, card_Model, hf6, hf2, hcardT]
  ring

theorem not_dvd_product_index (ι : normOne F × normOne F →* Model F)
    (hι : Function.Injective ι) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hd : r ∣ Nat.card F + 1) : ¬ r ∣ ι.range.index := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hnot2 : ¬ r ∣ 2 := fun h =>
    hr2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hr.ne_one)
  have hnot3 : ¬ r ∣ 3 := fun h =>
    hr3 ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hr.ne_one)
  have hnotq : ¬ r ∣ Nat.card F := by
    intro h
    have hh := Nat.dvd_sub hd h
    rw [Nat.add_sub_cancel_left] at hh
    exact hr.not_dvd_one hh
  have hminus : ¬ r ∣ Nat.card F - 1 := by
    intro h
    have hh := Nat.dvd_sub hd h
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hh
    exact hnot2 hh
  have hd2 : r ∣ Nat.card F ^ 2 - 1 := by
    rw [show Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1]
    exact dvd_mul_of_dvd_right hd _
  have hd4 : r ∣ Nat.card F ^ 4 - 1 := by
    have hh := hd2.trans (Nat.sub_one_dvd_pow_sub_one (Nat.card F ^ 2) 2)
    simpa only [← pow_mul] using hh
  have hquartic : ¬ r ∣ Nat.card F ^ 4 + Nat.card F ^ 2 + 1 := by
    intro h
    have hh := Nat.dvd_sub h (dvd_add hd4 hd2)
    rw [show Nat.card F ^ 4 + Nat.card F ^ 2 + 1 -
        ((Nat.card F ^ 4 - 1) + (Nat.card F ^ 2 - 1)) = 3 by
      have := Nat.one_le_pow 2 (Nat.card F) hq
      have := Nat.one_le_pow 4 (Nat.card F) hq
      omega] at hh
    exact hnot3 hh
  rw [product_index ι hι]
  exact hr.not_dvd_mul
    (hr.not_dvd_mul (fun h => hnotq (hr.dvd_of_dvd_pow h))
      (fun h => hminus (hr.dvd_of_dvd_pow h))) hquartic

/-- The constructed torus has order `(q+1)²`, contains a full Sylow subgroup,
and has the required independent inversion inside the actual G₂ model. -/
theorem exists_nonsplit_torus_sylow
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F + 1) :
    ∃ (ι : normOne F × normOne F →* Model F) (w : Model F) (P : Sylow r (Model F)),
      Function.Injective ι ∧ Nat.card ι.range = (Nat.card F + 1)^2 ∧
      (P : Subgroup (Model F)) ≤ ι.range ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ c, w * ι (1,c) * w⁻¹ = ι (1,c)) := by
  obtain ⟨ι, w, hi, hinv, hfix⟩ := exists_nonsplit_product (F := F)
  obtain ⟨R : Sylow r ι.range⟩ := Sylow.nonempty (p := r) (G := ι.range)
  let Q : Subgroup (Model F) := (R : Subgroup ι.range).map ι.range.subtype
  have hQp : IsPGroup r Q := R.isPGroup'.map ι.range.subtype
  have hQi : ¬ r ∣ Q.index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : r.Prime).not_dvd_mul R.not_dvd_index
      (not_dvd_product_index ι hi Fact.out (by omega) (by omega) hd)
  refine ⟨ι, w, hQp.toSylow hQi, hi, ?_, Subgroup.map_subtype_le _, hinv, hfix⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
    Nat.card_prod, card_normOne, pow_two]

theorem exists_inverted_sylow_of_dvd_add_one
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F + 1) :
    ∃ P : Sylow r (Model F), Nonempty (InvertedGenerators (P : Subgroup (Model F))) := by
  obtain ⟨ι, w, _, hi, _, _, hinv, hfix⟩ := exists_nonsplit_torus_sylow hr hd
  exact ProductTori.exists_inverted_sylow_of_product_index ι hi
    (not_dvd_product_index ι hi Fact.out (by omega) (by omega) hd) w hinv hfix

end QuadraticTorus

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem not_dvd_card_universal_kernel_of_dvd_add_one
    (hF : 4 < Nat.card F) {r : ℕ} [Fact r.Prime]
    (hr : 3 < r) (hd : r ∣ Nat.card F + 1) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  obtain ⟨P, ⟨hP⟩⟩ := QuadraticTorus.exists_inverted_sylow_of_dvd_add_one hr hd
  exact PerfectCentralCovering.not_dvd_card_kernel_of_inverted_sylow (by omega) P hP
    (universalProjection (Model F)) (universalProjection_surjective _)
    (universalProjection_ker_le_center _)

end Atlas.G2.MultiplierOrdinary.Nondefining

end
