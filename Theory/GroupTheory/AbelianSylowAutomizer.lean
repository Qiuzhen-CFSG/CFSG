module

public import Theory.GroupTheory.SylowDetectsKernel
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Solvable

/-!
# The automizer of an abelian Sylow two-subgroup of rank two

Let S be a nontrivial abelian Sylow two-subgroup of a nonsolvable finite
simple group. Its normalizer acts nontrivially on S, since otherwise
Burnside transfer gives a normal two-complement, contradicting simplicity.
The action image has odd order because S lies in its kernel. If S has
Klein four Frattini quotient, the action on that quotient is faithful:
the Burnside basis kernel is a two-group, detected on the Sylow subgroup.
The image order therefore divides six and is exactly three.

These are the transfer and automorphism inputs to the abelian Sylow step
in Janko–Thompson, Math. Z. 113 (1970), §6, p.394. Brauer's separate
homocyclic Sylow theorem is not used or asserted here.
-/

open Subgroup
open scoped IsMulCommutative

namespace Sylow

private theorem normalizer_action_on_sylow_eq_one
    {G : Type*} [Group G] (S : Sylow 2 G) [IsMulCommutative S]
    (s : S.subtype (le_normalizer : (S : Subgroup G) ≤ normalizer (S : Set G))) :
    (S : Subgroup G).normalizerMonoidHom s = 1 := by
  apply MulEquiv.ext
  intro t
  apply Subtype.ext
  change (s.val : G) * (t : G) * (s.val : G)⁻¹ = (t : G)
  have hc := congrArg Subtype.val (mul_comm (⟨s.val, s.property⟩ : S) t)
  change (s.val : G) * (t : G) = (t : G) * (s.val : G) at hc
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

/-- The normalizer's action on an abelian Sylow two-subgroup has odd order. -/
public theorem odd_card_normalizer_action
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) [IsMulCommutative S] :
    Odd (Nat.card (S : Subgroup G).normalizerMonoidHom.range) := by
  let N := normalizer (S : Set G)
  let P : Sylow 2 N := S.subtype le_normalizer
  let f := (S : Subgroup G).normalizerMonoidHom
  have hle : (P : Subgroup N) ≤ f.ker := by
    intro s hs
    exact normalizer_action_on_sylow_eq_one S ⟨s, hs⟩
  have hdiv : Nat.card f.range ∣ (P : Subgroup N).index := by
    rw [← index_ker]
    exact index_dvd_of_le hle
  exact Nat.not_even_iff_odd.mp (fun h => P.not_dvd_index (h.two_dvd.trans hdiv))

/-- Burnside transfer excludes a trivial automizer for a nontrivial abelian
Sylow subgroup of a nonsolvable finite simple group. -/
public theorem normalizer_action_ne_bot_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) [IsMulCommutative S]
    (hne : (S : Subgroup G) ≠ ⊥) :
    (S : Subgroup G).normalizerMonoidHom.range ≠ ⊥ := by
  intro hb
  have hf : (S : Subgroup G).normalizerMonoidHom = 1 :=
    MonoidHom.range_eq_bot_iff.mp hb
  have hNC : normalizer (S : Set G) ≤ centralizer (S : Set G) := by
    intro n hn
    have hk : (⟨n, hn⟩ : normalizer (S : Set G)) ∈
        (S : Subgroup G).normalizerMonoidHom.ker := by
      change (S : Subgroup G).normalizerMonoidHom ⟨n, hn⟩ = 1
      rw [hf]
      rfl
    rwa [normalizerMonoidHom_ker] at hk
  let f := MonoidHom.transferSylow S hNC
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact hns (Group.isSolvable_of_isSolvable_injective
      ((MonoidHom.ker_eq_bot_iff f).mp hbot))
  · have hdis := (MonoidHom.ker_transferSylow_isComplement' S hNC).disjoint
    change Disjoint f.ker (S : Subgroup G) at hdis
    exact hne (by simpa only [htop, top_inf_eq] using hdis.eq_bot)

/-- A nontrivial automizer has order three when the abelian Sylow subgroup
has a Klein four Frattini quotient. No simplicity hypothesis is needed. -/
public theorem card_normalizer_action_eq_three
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) [IsMulCommutative S]
    [IsKleinFour (S ⧸ frattini S)]
    (hne : (S : Subgroup G).normalizerMonoidHom.range ≠ ⊥) :
    Nat.card (S : Subgroup G).normalizerMonoidHom.range = 3 := by
  let N := normalizer (S : Set G)
  let P : Sylow 2 N := S.subtype le_normalizer
  let f := (S : Subgroup G).normalizerMonoidHom
  let q := quotientAut (frattini S)
  have hi : Function.Injective (q.comp f.range.subtype) :=
    P.injective_on_range_of_isPGroup_kernel f q
      (isPGroup_quotientAut_frattini_kernel S.isPGroup')
      (fun s _ => normalizer_action_on_sylow_eq_one S s)
  have hd : Nat.card f.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut (S ⧸ frattini S)]
    exact card_dvd_of_injective _ hi
  have ho := S.odd_card_normalizer_action
  have hn : Nat.card f.range ≠ 1 := by
    intro h
    exact hne (card_eq_one.mp h)
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
  change Odd (Nat.card f.range) at ho
  have hmod := Nat.odd_iff.mp ho
  change Nat.card f.range = 3
  interval_cases h : Nat.card f.range <;> simp_all

/-- The automizer has order three when the abelian Sylow subgroup of a
nonsolvable simple group has a Klein four Frattini quotient. -/
public theorem card_normalizer_action_eq_three_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) [IsMulCommutative S]
    [IsKleinFour (S ⧸ frattini S)] (hne : (S : Subgroup G) ≠ ⊥) :
    Nat.card (S : Subgroup G).normalizerMonoidHom.range = 3 :=
  S.card_normalizer_action_eq_three (S.normalizer_action_ne_bot_of_simple hns hne)

/-- The normalizer supplies an automorphism of order three in the rank-two
abelian Sylow case. -/
public theorem exists_order_three_normalizer_automorphism_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) [IsMulCommutative S]
    [IsKleinFour (S ⧸ frattini S)] (hne : (S : Subgroup G) ≠ ⊥) :
    ∃ a : MulAut S, a ∈ (S : Subgroup G).normalizerMonoidHom.range ∧ orderOf a = 3 := by
  have hcard := S.card_normalizer_action_eq_three_of_simple hns hne
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card (S : Subgroup G).normalizerMonoidHom.range by rw [hcard])
  exact ⟨a, a.property, by simpa only [Subgroup.orderOf_coe] using ha⟩

end Sylow
