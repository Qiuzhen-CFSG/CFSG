module

public import Theory.GroupTheory.CyclicThreeNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Odd-order normalizers of a subgroup of order three

An odd-order subgroup normalizing a cyclic group of order three centralizes
it. The conjugation image lies in the automorphism group of order two and
also has order dividing the odd-order actor, so its order is one.

This is the elementary group-theoretic step used to centralize local
order-three commutators by the odd action kernel in Stellmacher (1.6),
journal p.18; see `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

public theorem commutator_eq_bot_of_odd_normalizes_card_three
    {G : Type*} [Group G] [Finite G]
    (F Q : Subgroup G) (hF : Nat.card F = 3)
    (hQ : Nat.Coprime 2 (Nat.card Q))
    (hnorm : Q ≤ normalizer (F : Set G)) : ⁅F, Q⁆ = ⊥ := by
  let _ : IsCyclic F := isCyclic_of_prime_card hF
  have hAut : Nat.card (MulAut F) = 2 := by
    rw [IsCyclic.card_mulAut, hF, Nat.totient_prime Nat.prime_three]
  let φ : Q →* MulAut F := F.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hdiv2 : Nat.card φ.range ∣ 2 := by
    rw [← hAut]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hdivQ : Nat.card φ.range ∣ Nat.card Q := Subgroup.card_range_dvd φ
  have hcard : Nat.card φ.range = 1 := by
    have hdiv := Nat.dvd_gcd hdiv2 hdivQ
    rw [hQ.gcd_eq_one] at hdiv
    exact Nat.eq_one_of_dvd_one hdiv
  have hrange : φ.range = ⊥ := Subgroup.card_eq_one.mp hcard
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro f hf
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hφ : φ ⟨q, hq⟩ = 1 := by
    have hmem : φ ⟨q, hq⟩ ∈ φ.range := ⟨⟨q, hq⟩, rfl⟩
    rw [hrange] at hmem
    exact hmem
  have heq := congrArg (fun z : MulAut F => (z ⟨f, hf⟩ : G)) hφ
  change q * f * q⁻¹ = f at heq
  have heq' := congrArg (fun z : G => z * q) heq
  simpa [mul_assoc] using heq'

end Subgroup

