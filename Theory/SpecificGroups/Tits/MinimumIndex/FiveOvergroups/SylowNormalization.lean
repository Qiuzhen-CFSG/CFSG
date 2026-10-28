module

public import Theory.SpecificGroups.Tits.FiveFrobenius.Subgroups
public import Theory.SpecificGroups.Tits.Atlas1600Order
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum

/-!
# Normalizing the Sylow five-subgroup in a Tits overgroup

The existing five-kernel has order 25, and the ambient order has exactly two
factors of five. It is therefore Sylow. Sylow's first theorem supplies a
subgroup of order 25 inside any subgroup whose order is divisible by 25;
Sylow conjugacy carries that subgroup onto the literal five-kernel.

This only normalizes the input for the ATLAS max4/max8 coverage argument.
It does not assert any overgroup classification. The concrete order sources
are documented in `Atlas1600Order` and `FiveFrobenius.Subgroups`.
-/

namespace Tits.MinimumIndexFiveOvergroups
open Subgroup
open scoped Pointwise

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_not_dvd_index (Q : Subgroup Atlas1600Group)
    (hQ : Nat.card Q = 25) : ¬ 5 ∣ Q.index := by
  have h := Q.card_mul_index
  rw [hQ, atlas1600Group_card] at h
  have hi : Q.index = 718848 := by omega
  rw [hi]
  decide

/-- The existing concrete five-kernel is Sylow in the ambient group. -/
public noncomputable def sylowFive : Sylow 5 Atlas1600Group :=
  (IsPGroup.of_card (p := 5) (n := 2) FiveFrobenius.kernel_card).toSylow
    (five_not_dvd_index _ FiveFrobenius.kernel_card)

public theorem sylowFive_coe : (sylowFive : Subgroup Atlas1600Group) =
    FiveFrobenius.kernel := by rfl

/-- Every subgroup with order divisible by 25 can be conjugated to contain
our literal five-kernel; no properness hypothesis is required. -/
public theorem exists_conjugate_contains_kernel (L : Subgroup Atlas1600Group)
    (h25 : 25 ∣ Nat.card L) : ∃ g : Atlas1600Group,
      FiveFrobenius.kernel ≤ L.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := L) 5 (n := 2) h25
  have hc : Nat.card (Q.map L.subtype) = 25 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hQ]
    norm_num
  let P : Sylow 5 Atlas1600Group :=
    (IsPGroup.of_card (p := 5) (n := 2) hc).toSylow (five_not_dvd_index _ hc)
  have hPL : (P : Subgroup Atlas1600Group) ≤ L := map_subtype_le Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group P sylowFive
  refine ⟨g, ?_⟩
  rw [← sylowFive_coe, ← hg]
  change (P : Subgroup Atlas1600Group).map (MulAut.conj g).toMonoidHom ≤ _
  exact map_mono hPL

end Tits.MinimumIndexFiveOvergroups
