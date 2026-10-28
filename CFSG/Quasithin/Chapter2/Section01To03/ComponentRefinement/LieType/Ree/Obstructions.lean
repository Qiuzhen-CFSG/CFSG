module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions

/-!
# Two local obstructions for the Ree calculation

An allowed χ₀ block has quotient order divisible by three. Thus a parabolic
of order prime to three contains none. For the other parabolic, shortness
forces [[Q,B],Q] = 1 whenever Q lies in the actual two-core of B. A concrete
nonzero third commutator therefore excludes a short block.

These are necessary conditions on actual subgroups, not an identification of
whole parabolics with blocks. They support the two-parabolic argument of
Aschbacher–Smith 2.3.9(7), printed p.526; shortness is C.1.7, printed p.123.
The Ree and Tits local-overgroup calculations remain separate obligations.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

variable {K : Type*} [Group K]

/-- Every allowed block quotient has order divisible by three. -/
theorem three_dvd_quotient_card (h : IsChiZeroBlock K) : 3 ∣ Nat.card (K ⧸ pCore 2 K) := by
  rcases chiZero_order_module h with ⟨n, _, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]
    have hd := Nat.sub_one_dvd_pow_sub_one 4 n
    change 3 ∣ (2 ^ 2) ^ n - 1 at hd
    rw [← pow_mul] at hd
    exact dvd_mul_of_dvd_right hd _
  · rw [he]
  · rw [he]; decide

/-- A group of order prime to three contains no subgroup of an allowed block type. -/
theorem not_chiZero_subgroup_of_three_free {G : Type*} [Group G]
    (hG : ¬ 3 ∣ Nat.card G) (B : Subgroup G) :
    ¬ IsChiZeroBlock B := by
  intro hb
  exact hG (((three_dvd_quotient_card hb).trans (pCore 2 B).card_quotient_dvd_card).trans
    B.card_subgroup_dvd_card)

/-- The obstruction persists after adjoining a normal two-subgroup.
The quotient is the actual quotient by the specified normal subgroup. -/
theorem not_chiZero_subgroup_of_two_extension {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hquot : ¬ 3 ∣ Nat.card (G ⧸ Q)) (B : Subgroup G) :
    ¬ IsChiZeroBlock B := by
  apply not_chiZero_subgroup_of_three_free (B := B)
  intro hthree
  rw [← Q.card_mul_index] at hthree
  rcases Nat.prime_three.dvd_mul.mp hthree with hcore | hindex
  · obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [hn] at hcore
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hcore)
  · exact hquot (Q.index_eq_card ▸ hindex)

/-- Every two-core sublayer of a short subgroup has zero third commutator.
The core and both commutators are viewed in the common ambient group. -/
theorem third_commutator_eq_bot_of_short {G : Type*} [Group G] {B Q : Subgroup G}
    (hb : IsShort B) (hQ : Q ≤ B.pCoreIn 2) : ⁅⁅Q, B⁆, Q⁆ = ⊥ := by
  have hc : ⁅⁅B.pCoreIn 2, B⁆, B.pCoreIn 2⁆ = ⊥ := by
    have hi : ⁅⁅pCore 2 B, (⊤ : Subgroup B)⁆, pCore 2 B⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr hb.central
    have hm := congrArg (Subgroup.map B.subtype) hi
    simpa only [pCoreIn, map_commutator, Subgroup.map_bot, ← MonoidHom.range_eq_map, B.range_subtype]
      using hm
  apply le_bot_iff.mp
  exact hc ▸ commutator_mono (commutator_mono hQ le_rfl) hQ

variable {G : Type*} [Group G]

/-- A concrete normal two-layer with a noncentral commutator. The layer is
relative to B, with every subgroup and commutator in the same ambient group. -/
def HasNoncentralTwoLayer (B : Subgroup G) : Prop :=
  ∃ Q : Subgroup G, IsPGroup 2 Q ∧ Q ≤ B ∧
    B ≤ normalizer (Q : Set G) ∧ ⁅⁅Q, B⁆, Q⁆ ≠ ⊥

/-- It suffices to identify a normal two-layer; equality with O₂(B) is not
needed to contradict the central-layer condition in the short-group definition. -/
theorem not_short_of_noncentral_two_layer {B : Subgroup G}
    (h : HasNoncentralTwoLayer B) : ¬ IsShort B := by
  obtain ⟨Q, hQ, hQB, hn, hc⟩ := h
  intro hb
  exact hc (third_commutator_eq_bot_of_short hb
    (le_pCoreIn_of_normalizes hQ hQB hn))

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
