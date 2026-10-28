module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupTheory.PrimeRankElementary

/-!
# A coarse intrinsic two-rank bound for Hall--Janko

The exact carrier order is 604800, with two-part `2^7`. The order of every
elementary abelian two-subgroup divides it, giving the rank bound seven.
This is sufficient for the elementary-layer action in the ordinary J₂ row
of Aschbacher--Smith C.4.8, printed pp.153--154.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2

/-- The exact J₂ carrier has two-rank at most seven, by its order. -/
theorem primeRank_two_le_seven : primeRank 2 Carrier ≤ 7 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply (primeRank_le_iff_elementary_card_le Carrier).mpr
  intro E hE
  let := hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hd : Nat.card E ∣ Nat.card Carrier := E.card_subgroup_dvd_card
  rw [hn, ExceptionalParabolics.FirstParabolic.card_carrier] at hd
  have hnle : n ≤ 7 := by
    by_contra! hlarge
    have hpow : 2 ^ 8 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have hnot : ¬ 2 ^ 8 ∣ 604800 := by norm_num
    exact hnot (hpow.trans hd)
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hnle

end Sporadic.LeechRelated.J2
