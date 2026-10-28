module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import Mathlib.GroupTheory.Complement

/-!
# Hall arithmetic in the unique maximal overgroup

An odd Hall subgroup and the specified Sylow two-subgroup have coprime
orders whose product is the order of the overgroup. Both products are
therefore the whole overgroup. Restriction and inclusion give permutation
with the original Sylow, without any conjugation choice.

`intrinsicOfHall` applies this arithmetic to actual model subgroups. It
still requires the model proofs of abelianness, the cyclic subgroup, maximal
solvability and the Frattini factorization. It is a construction helper,
not a replacement for E.2.2 or a completed proof of E.6.27.
Source: Aschbacher--Smith, E.3.37, E.6.27 and 4.4.13, pp.239, 257, 623--624.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterB
universe u
variable {X : Type u} [Group X] [Finite X]

private theorem oddHall_complement_sylow (Y : Subgroup X)
    (hY : IsHallSubgroup oddPrimes Y) (S : Sylow 2 X) :
    (S : Subgroup X).IsComplement' Y := by
  have hYtwo : ¬ 2 ∣ Nat.card Y := fun h =>
    hY.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h rfl
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hcop_cards : Nat.Coprime (Nat.card Y) (Nat.card S) := by
    rw [hn]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hYtwo).symm.pow_right n
  have hcop_indices : Nat.Coprime (S : Subgroup X).index Y.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpS hpY
    have hp2 : p = 2 := Classical.not_not.mp
      (hY.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpY)
    exact S.not_dvd_index (hp2 ▸ hpS)
  have hcard_dvd_index : Nat.card Y ∣ (S : Subgroup X).index := by
    have hdvd : Nat.card Y ∣ (S : Subgroup X).index * Nat.card S := by
      simpa only [index_mul_card] using card_subgroup_dvd_card Y
    exact hcop_cards.dvd_of_dvd_mul_right hdvd
  have hindex_dvd_card : (S : Subgroup X).index ∣ Nat.card Y := by
    have hdvd : (S : Subgroup X).index ∣ Nat.card Y * Y.index := by
      simpa only [card_mul_index] using (S : Subgroup X).index_dvd_card
    exact hcop_indices.dvd_of_dvd_mul_right hdvd
  have hcardY : Nat.card Y = (S : Subgroup X).index :=
    Nat.dvd_antisymm hcard_dvd_index hindex_dvd_card
  refine isComplement'_of_coprime ?_ hcop_cards.symm
  rw [hcardY]
  exact (S : Subgroup X).card_mul_index

/-- The odd Hall subgroup of an overgroup permutes with the original Sylow
subgroup: both products are the whole overgroup. No Sylow conjugation occurs. -/
theorem hall_permutation (S : Sylow 2 X) {M Y : Subgroup X}
    (hSM : (S : Subgroup X) ≤ M) (hYM : Y ≤ M)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf M)) :
    (Y : Set X) * (S : Set X) = (S : Set X) * (Y : Set X) := by
  have hc := oddHall_complement_sylow (Y.subgroupOf M) hY (S.subtype hSM)
  have he : ((Y.subgroupOf M : Subgroup M) : Set M) * (S.subtype hSM : Set M) =
      (S.subtype hSM : Set M) * ((Y.subgroupOf M : Subgroup M) : Set M) :=
    hc.symm.mul_eq.trans hc.mul_eq.symm
  have hi := congrArg (Set.image M.subtype) he
  rw [Set.image_mul, Set.image_mul] at hi
  change (((Y.subgroupOf M).map M.subtype : Subgroup X) : Set X) *
      ((((S : Subgroup X).subgroupOf M).map M.subtype : Subgroup X) : Set X) =
    ((((S : Subgroup X).subgroupOf M).map M.subtype : Subgroup X) : Set X) *
      (((Y.subgroupOf M).map M.subtype : Subgroup X) : Set X) at hi
  simpa only [map_subgroupOf_eq_of_le hYM, map_subgroupOf_eq_of_le hSM,
    Sylow.coe_coe] using hi

/-- Constructor for the intrinsic output from actual subgroups. Hall arithmetic
supplies oddness and permutation; the model calculation must supply the
abelian torus overgroup, maximal solvability, and normalizer factorization. -/
noncomputable def intrinsicOfHall (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (n : ℕ) (Y B Q : Subgroup X)
    (hY : Y ≤ minimalParabolicMax S hP)
    (hHall : IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)))
    (ha : IsMulCommutative Y) (hB : B ≤ Y) (hc : IsCyclic B)
    (hcard : Nat.card B = 2 ^ n - 1)
    (hsolv : Group.IsSolvable (minimalParabolicMax S hP))
    (hQ : Y ≤ normalizer (Q : Set X))
    (hfrat : (S : Set X) = (Q : Set X) *
      ((S : Subgroup X) ⊓ normalizer (Y : Set X) : Set X)) :
    IntrinsicHallCartanData S hP n where
  witness := {
    abelianGroup := Y
    cyclicGroup := B
    sylow := S
    cyclic_le := hB
    abelian := ha
    odd := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro htwo
      have hcardY := Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
      exact hHall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ (hcardY ▸ htwo) rfl
    cyclic := hc
    card := hcard
    permutes := hall_permutation S (minimalParabolicMax_spec S hP).2 hY hHall }
  sylow_eq := rfl
  hall_le := hY
  hall := hHall
  maximal_solvable := hsolv
  twoGroup := Q
  normalizes := hQ
  frattini := hfrat

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
