module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Order obstructions from the full rank-two Frattini shadow

If YS has the S₃ × S₃ quotient of 15.3.41 and S is Sylow in the ambient
group, every subgroup M containing YS has order divisible by 36 and at
least 36 times the order of O₂(M). The latter core lies in S and hence
in O₂(YS), which lies in the preimage of the Frattini subgroup of
YS/O₂(YS). Counting that actual quotient gives the lower bound.

These bounds preserve the O_{2,Φ} denominator. They do not replace it
with O₂ or assert any model coverage. In J₂ they eliminate the first
local candidate by divisibility and the second by its core order.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.41--42, printed p.1138; the O_{2,Φ} convention is on p.491.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem shadow_index {Y S : Subgroup H} (h : RankTwoShadow Y S) :
    (twoFrattiniCore (Y ⊔ S : Subgroup H)).index = 36 := by
  obtain ⟨e⟩ := h
  change Nat.card ((Y ⊔ S : Subgroup H) ⧸ twoFrattiniCore (Y ⊔ S : Subgroup H)) = 36
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

omit [Finite H] in
private theorem core_le_frattiniCore : pCore 2 H ≤ twoFrattiniCore H := by
  intro x hx
  change QuotientGroup.mk' (pCore 2 H) x ∈ frattini (H ⧸ pCore 2 H)
  rw [show QuotientGroup.mk' (pCore 2 H) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

/-- Every local overgroup containing the specified Sylow subgroup has order
divisible by 36 and at least 36 times its intrinsic two-core order. -/
theorem shadow_local_order_bounds (P : Sylow 2 H) (M Y S : Subgroup H)
    (hP : (P : Subgroup H) = S) (hS : S ≤ M) (hY : Y ≤ M)
    (hshadow : RankTwoShadow Y S) :
    36 ∣ Nat.card M ∧ 36 * Nat.card (pCore 2 M) ≤ Nat.card M := by
  let U : Subgroup M := Y.subgroupOf M ⊔ S.subgroupOf M
  have hsh := rankTwoShadow_subgroupOf hY hS hshadow
  have hi : (twoFrattiniCore U).index = 36 := shadow_index hsh
  refine ⟨(hi ▸ (twoFrattiniCore U).index_dvd_card).trans (card_subgroup_dvd_card U), ?_⟩
  have hPU : ((P.subtype (hP.symm ▸ hS) : Sylow 2 M) : Subgroup M) ≤ U := by
    intro x hx
    exact (show S.subgroupOf M ≤ U from le_sup_right) (hP ▸ hx)
  have hle := pCore_le_map_of_sylow_le (P.subtype (hP.symm ▸ hS)) U hPU
  have hc : Nat.card (pCore 2 M) ≤ Nat.card (twoFrattiniCore U) := by
    calc
      _ ≤ Nat.card ((pCore 2 U).map U.subtype) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      _ = Nat.card (pCore 2 U) := card_map_of_injective U.subtype_injective
      _ ≤ Nat.card (twoFrattiniCore U) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion core_le_frattiniCore)
          (Subgroup.inclusion_injective core_le_frattiniCore)
  calc
    36 * Nat.card (pCore 2 M) ≤ 36 * Nat.card (twoFrattiniCore U) := Nat.mul_le_mul_left _ hc
    _ = Nat.card U := by rw [mul_comm, ← hi, (twoFrattiniCore U).card_mul_index]
    _ ≤ Nat.card M := card_le_card_group U


end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve
