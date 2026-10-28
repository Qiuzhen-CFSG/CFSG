module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders

/-!
# Excluding large two-group extensions of A₅ in the Tits group

The certified order-64 seed catalogue places an even-index subgroup whose
order is divisible by neither 25 nor 13 into a parabolic. An odd-index
subgroup contains an ambient Sylow two-subgroup and uses the established
Sylow-overgroup cover. Hence no subgroup has order 60 · 2^n for n ≥ 4:
the parabolic orders 10240 and 6144 are not divisible by fifteen.

The result is stated on both the finite permutation carrier and the
literal Parrott presentation, using their proved marked equivalence.
Source: Parrott (1972), §5, p.683, and the primary ATLAS Tits subgroup
entry; the imported finite certificates establish the placements used here.
-/

public section

open Subgroup
open scoped Pointwise
namespace Tits
open ExceptionalParabolics

private theorem proper_large_two_placement (A : Subgroup Atlas1600Group)
    (hA : A ≠ ⊤) (h64 : 64 ∣ Nat.card A) (h25 : ¬ 25 ∣ Nat.card A)
    (h13 : ¬ 13 ∣ Nat.card A) :
    ∃ g : Atlas1600Group, A.map (MulAut.conj g).toMonoidHom ≤ first ∨
      A.map (MulAut.conj g).toMonoidHom ≤ second := by
  by_cases heven : 2 ∣ A.index
  · exact MinimumIndex.LargeTwoOvergroups.large_two_subgroup_placement A hA heven h64 h25 h13
  · let Q : Sylow 2 A := Classical.choice inferInstance
    let R := (Q : Subgroup A).map A.subtype
    have hp : IsPGroup 2 R := Q.isPGroup'.map A.subtype
    have hi : ¬ 2 ∣ R.index := by
      rw [index_map_subtype]
      exact fun h => (Nat.prime_two.dvd_mul.mp h).elim Q.not_dvd_index heven
    let P : Sylow 2 Atlas1600Group := hp.toSylow hi
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group P atlas1600SylowTwo
    have hS : atlas1600SylowTwoSubgroup ≤ A.map (MulAut.conj g).toMonoidHom := by
      rw [← atlas1600SylowTwo_coe, ← hg]
      exact map_mono (map_subtype_le (Q : Subgroup A))
    refine ⟨g, ConverseLocalCoverage.le_first_or_second _ ?_ hS⟩
    intro ht
    apply hA
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [map_top_of_surjective _ (MulAut.conj g).surjective]
    exact ht

/-- The Tits group has no subgroup of order sixty times a power of two
whose two-group factor has order at least sixteen. -/
theorem atlas_no_sixty_mul_two_pow (A : Subgroup Atlas1600Group)
    (n : ℕ) (hn : 4 ≤ n) (hc : Nat.card A = 60 * 2 ^ n) : False := by
  have h25 : ¬ 25 ∣ Nat.card A := by
    rw [hc]
    have hcop : Nat.Coprime 25 (2 ^ n) := (by decide : Nat.Coprime 25 2).pow_right n
    exact fun h => (by decide : ¬ 25 ∣ 60) (hcop.dvd_mul_right.mp h)
  have h13 : ¬ 13 ∣ Nat.card A := by
    rw [hc]
    intro h
    rcases (show Nat.Prime 13 by decide).dvd_mul.mp h with h60 | hp
    · exact (by decide : ¬ 13 ∣ 60) h60
    · exact (by decide : ¬ 13 ∣ 2) ((show Nat.Prime 13 by decide).dvd_of_dvd_pow hp)
  have hA : A ≠ ⊤ := by
    intro he
    rw [he, Nat.card_congr (topEquiv (G := Atlas1600Group)).toEquiv,
      atlas1600Group_card] at h13
    exact h13 (by decide)
  have h64 : 64 ∣ Nat.card A := by
    rw [hc]
    exact (by decide : 64 ∣ 60 * 2 ^ 4).trans
      (Nat.mul_dvd_mul_left 60 (Nat.pow_dvd_pow 2 hn))
  obtain ⟨g, hg⟩ := proper_large_two_placement A hA h64 h25 h13
  have h15 : 15 ∣ Nat.card A := by rw [hc]; exact dvd_mul_of_dvd_left (by decide) _
  rcases hg with hf | hs
  · have hdiv := card_dvd_of_le hf
    rw [card_map_of_injective (MulAut.conj g).injective] at hdiv
    have hd := h15.trans hdiv
    rw [first_card] at hd
    exact (by decide : ¬ 15 ∣ 10240) hd
  · have hdiv := card_dvd_of_le hs
    rw [card_map_of_injective (MulAut.conj g).injective] at hdiv
    have hd := h15.trans hdiv
    rw [second_card] at hd
    exact (by decide : ¬ 15 ∣ 6144) hd

/-- The same order exclusion on the literal Parrott presentation carrier. -/
theorem no_sixty_mul_two_pow (A : Subgroup ParrottGroup)
    (n : ℕ) (hn : 4 ≤ n) (hc : Nat.card A = 60 * 2 ^ n) : False := by
  apply atlas_no_sixty_mul_two_pow (A.map parrottFiniteImageEquiv.toMonoidHom) n hn
  rw [card_map_of_injective (f := parrottFiniteImageEquiv.toMonoidHom)
    parrottFiniteImageEquiv.injective]
  exact hc
end Tits
