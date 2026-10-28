module

public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteOrbits
public import Mathlib.GroupTheory.Nilpotent

/-!
# Parrott's core hypotheses in the actual Tits parabolic

The core has order 512 and its derived subgroup has centralizer of order 32.
A class-two core would centralize its own derived subgroup, contradicting
these orders. The existing marked five-fixed subgroup is central; counting
inside the first parabolic makes its actor a Sylow five-subgroup.

These are intrinsic facts about the concrete local group. Their recognition
consumer transports them to a full involution centralizer.

Source: Parrott (1972), original hypotheses, p.672; Aschbacher (1982),
(3.2.7), as implemented in the imported concrete parabolic calculations.
-/

public section
open Subgroup
namespace ReeTwo.ParabolicConcrete


/-- The actual Tits two-core is not of nilpotency class at most two. -/
theorem tits_core_class_lower : 3 ≤ Group.nilpotencyClass titsQ := by
  let : Group.IsNilpotent titsQ := (pCore_isPGroup (p := 2) (G := Tits.ExceptionalParabolics.first)).isNilpotent
  by_contra h
  have hc : Group.nilpotencyClass titsQ ≤ 2 := by omega
  have hD : commutator titsQ ≤ center titsQ :=
    commutator_top_right_eq_bot_iff_le_center.mp
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc)
  have he : (commutator titsQ).map titsQ.subtype = titsE := by
    rw [map_commutator_eq, range_subtype]
  have hle : titsQ ≤ titsF := by
    intro x hx y hy
    rw [← he] at hy
    obtain ⟨y,hy,rfl⟩ := hy
    exact (congrArg Subtype.val (mem_center_iff.mp (hD hy) ⟨x,hx⟩)).symm
  have hn := card_le_of_le hle
  rw [titsQ_card,titsF_card] at hn
  omega

/-- A Sylow five-subgroup has central fixed subgroup in the actual two-core. -/
theorem tits_sylow_five_fixed_center :
    ∃ P : Sylow 5 Tits.ExceptionalParabolics.first,
      (centralizer (P : Set Tits.ExceptionalParabolics.first)).subgroupOf titsQ ≤
        center titsQ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P := zpowers titsFive
  have hcard : Nat.card P = 5 := by rw [Nat.card_zpowers,titsFive_order]
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hi : P.index = 2048 := by
    have hcount := P.card_mul_index
    rw [hcard,Tits.ExceptionalParabolics.first_card] at hcount
    omega
  let S := hp.toSylow (by rw [hi]; decide)
  exact ⟨S,titsFiveFixed_le_center⟩

end ReeTwo.ParabolicConcrete
