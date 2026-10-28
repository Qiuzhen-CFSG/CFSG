module

public import Theory.GroupTheory.CentralPChiefFactors
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Binary chief factors of S₅ are central

Every nontrivial normal subgroup of S₅ contains A₅. Thus a normal section
with nontrivial denominator is central, since the commutator subgroup is A₅.
With trivial denominator, a nontrivial normal section contains A₅ and cannot
be a two-group: its order is divisible by three.

This allows the central C₂ chief factor above A₅. It does not assert that
S₅ has no binary chief factors. Source application: Aschbacher–Smith,
14.7.71(1), printed p.1075, the terminal H/O₂(H) contribution.
-/

public section
open Subgroup
namespace alternatingGroup

/-- Every actual binary S₅-chief interval is central. -/
theorem symmetric_five_hasCentralTwoChiefFactors :
    HasCentralPChiefFactors 2 (Equiv.Perm (Fin 5)) := by
  intro K L hK hL hlt _ hp
  let := hK
  let := hL
  by_cases hK0 : K = ⊥
  · subst K
    have hpL : IsPGroup 2 L := hp.of_equiv
      ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf L)).trans
        QuotientGroup.quotientBot)
    have hL0 : L ≠ ⊥ := ne_of_gt hlt
    have hAL := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5))
      ((Subgroup.nontrivial_iff_ne_bot L).mpr hL0)
    have hpA := hpL.of_injective (Subgroup.inclusion hAL) (Subgroup.inclusion_injective hAL)
    obtain ⟨n, hn⟩ := hpA.exists_card_dvd_pow
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
    rw [hc] at hn
    have hd : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hd
    norm_num at this
  · apply (map_mk_le_center_iff K L).mpr
    exact (commutator_mono le_rfl le_top).trans
      (alternatingGroup.commutator_perm_le.trans
        (Equiv.Perm.alternatingGroup_le_of_normal (by simp)
          ((Subgroup.nontrivial_iff_ne_bot K).mpr hK0)))

end alternatingGroup
