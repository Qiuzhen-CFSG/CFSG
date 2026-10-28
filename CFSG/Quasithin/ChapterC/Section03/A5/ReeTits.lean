module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.Tits.SixtyOrderSubgroups
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Native Ree and Tits exclusions for the deleted-five block

The block retains its actual alternating-five quotient and its
characteristic layer U of order sixteen. Hence its order is 60 · 2^n,
with n ≥ 4. In a large Ree group it normalizes U, contradicting the
three- or five-free order of the covering parabolic. In the Tits group,
the independently proved order exclusion already gives the contradiction.

The Ree fixed-group endpoint uses the original matrix-preserving model
equivalence. No bound on an ambient Sylow, centralizer equality, or
normalizer control is added to the block hypotheses.
Source: Aschbacher–Smith C.3.1 and 13.5.15, printed pp.149–150 and 921,
using the literal alternating-five block defined in C.1.12.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

private theorem alternatingFive_order (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) :
    ∃ n : ℕ, 4 ≤ n ∧ Nat.card A = 60 * 2 ^ n := by
  obtain ⟨e⟩ := hA.2.2.quotient_iso
  have hquot : Nat.card (A ⧸ pCore 2 A) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hU : Nat.card (blockU A) = 16 := by
    rwa [card_map_of_injective A.subtype_injective] at hc
  have hle : 2 ^ 4 ≤ 2 ^ n := by
    rw [← hn]
    change 16 ≤ Nat.card (pCore 2 A)
    rw [← hU]
    exact Nat.card_le_card_of_injective (inclusion blockU_le_core)
      (inclusion_injective blockU_le_core)
  refine ⟨n, (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle, ?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A), hquot, hn]

/-- The literal deleted-five block with its order-sixteen U cannot lie in
an actual large Ree group. -/
theorem native_reeF4_no_alternatingFive {m : ℕ} (hm : 1 ≤ m)
    (A : Subgroup (ReeF4.Model m)) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  let U := (blockU A).map A.subtype
  have hU : U ≠ ⊥ := by
    intro he
    change Nat.card U = 16 at hc
    rw [he, card_bot] at hc
    omega
  have hp : IsPGroup 2 U := IsPGroup.of_card (n := 4) hc
  have hAN : A ≤ normalizer (U : Set (ReeF4.Model m)) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (blockU A))
  obtain ⟨n, _, hn⟩ := alternatingFive_order A hA hc
  have h15 : 15 ∣ Nat.card A := by rw [hn]; exact dvd_mul_of_dvd_left (by decide) _
  exact ReeF4.ConverseParabolics.normalizer_fifteen_free hm U hU hp
    (h15.trans (card_dvd_of_le hAN))

/-- Transport to a large Ree model retains the original block and its
characteristic commutator layer. -/
theorem no_alternatingFive_of_reeF4_equiv {m : ℕ} (hm : 1 ≤ m)
    (e : G ≃* ReeF4.Model m) (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  let B := A.map e.toMonoidHom
  let a : A ≃* B := e.subgroupMap A
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a hA
  have hU : (blockU B).map B.subtype = ((blockU A).map A.subtype).map e.toMonoidHom := by
    rw [← RankOne.Solvable.blockU_map_equiv a, map_map, map_map]
    rfl
  apply native_reeF4_no_alternatingFive hm B hB
  rw [hU, card_map_of_injective e.injective]
  exact hc

/-- The same exclusion for any actual local Ree fixed-group realization. -/
theorem native_reeF4_fixedGroup_no_alternatingFive {m : ℕ} (hm : 1 ≤ m)
    (d : ReeF4.LocalBlockInput m) (A : Subgroup d.fixedGroup)
    (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False :=
  no_alternatingFive_of_reeF4_equiv hm d.modelEquiv A hA hc

/-- The intrinsic order exclusion applies directly to the original
Parrott carrier and deleted-five block. -/
theorem native_tits_no_alternatingFive (A : Subgroup Tits.ParrottGroup)
    (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  obtain ⟨n, hn, he⟩ := alternatingFive_order A hA hc
  exact Tits.no_sixty_mul_two_pow A n hn he

/-- Any group isomorphic to the actual Tits group has the same block exclusion. -/
theorem no_alternatingFive_of_tits_equiv (e : G ≃* Tits.ParrottGroup)
    (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16) : False := by
  obtain ⟨n, hn, he⟩ := alternatingFive_order A hA hc
  apply Tits.no_sixty_mul_two_pow (A.map e.toMonoidHom) n hn
  rw [card_map_of_injective e.injective]
  exact he
end CFSG.Quasithin.ChapterC
