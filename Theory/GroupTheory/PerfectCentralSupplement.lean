module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Central supplements in perfect finite groups

Transfer to the abelianization of a subgroup H raises central elements to
[G:H]. Perfectness kills transfer; when this index is prime to p it follows
that every central p-element of H lies in its derived subgroup. Consequently
a central p-subgroup cannot be a proper supplement at prime-to-p index.

This retains the full kernel in the central-cover Borel calculation in
Aschbacher--Smith, 15.3.38, printed p.1136. The argument is general finite
group transfer, independent of the matrix model or any splitting theorem.
-/

public section
namespace Subgroup

/-- A central p-subgroup of a perfect finite group lies in the derived subgroup
of every overgroup whose index is prime to p. -/
theorem central_pSubgroup_le_commutator {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (H K : Subgroup G)
    (hKH : K ≤ H) (hKZ : K ≤ center G) (hKp : IsPGroup p K)
    (hi : ¬ p ∣ H.index) : K ≤ ⁅H,H⁆ := by
  intro k hk
  let kH : H := ⟨k, hKH hk⟩
  have hz : k ∈ center G := hKZ hk
  have ht := MonoidHom.transfer_eq_pow (H := H) (Abelianization.of : H →* Abelianization H) k
    (fun i g _ => by
      rw [mem_center_iff.mp (pow_mem hz i) g⁻¹, mul_assoc, inv_mul_cancel, mul_one])
  have hv : MonoidHom.transfer (Abelianization.of : H →* Abelianization H) k = 1 :=
    Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
  have hm : kH ^ H.index ∈ _root_.commutator H := by
    rw [← Abelianization.ker_of]
    exact ht.symm.trans hv
  have hp : k ^ H.index ∈ ⁅H,H⁆ := by
    rw [← map_subtype_commutator]
    exact mem_map_of_mem H.subtype hm
  obtain ⟨a, ha⟩ := hKp.exists_orderOf_dvd_pow ⟨k,hk⟩
  rw [← Subgroup.orderOf_coe] at ha
  have hc : H.index.Coprime (orderOf k) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hi).symm.pow_right a |>.of_dvd_right ha
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hc
  exact hm ▸ (⁅H,H⁆).pow_mem hp m

open scoped IsMulCommutative in
/-- A central p-kernel cannot enlarge a subgroup to prime-to-p index
in a perfect finite group. No splitting of the central extension is assumed. -/
theorem sup_central_pSubgroup_eq {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (N K : Subgroup G)
    (hKZ : K ≤ center G) (hKp : IsPGroup p K)
    (hi : ¬ p ∣ (N ⊔ K).index) : N ⊔ K = N := by
  let H := N ⊔ K
  have hNH : N ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have hHN : H ≤ normalizer (N : Set G) :=
    sup_le N.le_normalizer (hKZ.trans (center_le_normalizer _))
  let : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hKZH : K.subgroupOf H ≤ center H := by
    intro k hk
    exact mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp (hKZ hk) x))
  have hgen : N.subgroupOf H ⊔ center H = ⊤ := by
    apply top_unique
    rw [← subgroupOf_self H, show H = N ⊔ K from rfl, subgroupOf_sup hNH hKH]
    exact sup_le_sup_left hKZH _
  have hc : ⁅H,H⁆ ≤ N := by
    rw [← map_subtype_commutator, ← map_subgroupOf_eq_of_le hNH]
    exact map_mono (Normal.commutator_le_of_self_sup_commutative_eq_top hgen inferInstance)
  apply le_antisymm _ le_sup_left
  exact sup_le le_rfl ((central_pSubgroup_le_commutator H K hKH hKZ hKp hi).trans hc)

end Subgroup
