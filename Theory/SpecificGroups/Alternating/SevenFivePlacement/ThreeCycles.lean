module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
/-!
# Cubic cycle type in a full-Sylow-normalized A₅

The original A₅ fixes two letters. An element of order three therefore has
support at most five, so its cycle type has one three-cycle rather than two.
This is the cubic form of the C.5.13 restriction comparison.
-/
public section
open Subgroup MulAction
namespace Theory.SpecificGroups.Alternating.SevenFivePlacement
local notation "A7" => alternatingGroup (Fin 7)
theorem isThreeCycle_of_order_three (B : Subgroup A7)
    (e : B ≃* alternatingGroup (Fin 5)) (S : Sylow 2 A7)
    (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7))
    (a : B) (ha : orderOf a = 3) : a.val.val.IsThreeCycle := by
  classical
  have hfixed : fixedPoints B (Fin 7) ⊆ (a.val.val.support : Set (Fin 7))ᶜ := by
    intro i hi
    exact Equiv.Perm.notMem_support.mpr (hi a)
  have hh := Set.ncard_le_ncard hfixed
  rw [fixed_card_two B e S hSN] at hh
  have hc := Set.ncard_add_ncard_compl (a.val.val.support : Set (Fin 7))
  rw [Nat.card_fin, Set.ncard_coe_finset] at hc
  have hs : a.val.val.support.card ≤ 5 := by omega
  have ho : orderOf a.val.val = 3 := (Subgroup.orderOf_coe a.val).trans ((Subgroup.orderOf_coe a).trans ha)
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (show (orderOf a.val.val).Prime by rw [ho]; decide)
  have hsum := Equiv.Perm.sum_cycleType a.val.val
  rw [hn, ho, Multiset.sum_replicate, nsmul_eq_mul] at hsum
  norm_num at hsum
  have hn0 : n = 0 := by omega
  apply card_support_eq_three_iff.mp
  simpa [hn0] using hsum.symm
end Theory.SpecificGroups.Alternating.SevenFivePlacement
