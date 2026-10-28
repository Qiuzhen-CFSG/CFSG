module
public import Theory.GroupTheory.InvariantMaximalGeneration
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# Subgroups surjecting across a central derived kernel

A central kernel in the derived subgroup cannot supplement a proper subgroup:
the derived subgroup of a central product is already in the other factor.
Central Sylow transfer supplies exactly this kernel containment for the
restriction of a perfect central cover to an actual Sylow subgroup.

Source application: the exceptional central-cover lifting in
Aschbacher--Smith 2.5.7, printed p.556.
-/
public section

open Subgroup
namespace Subgroup
variable {G B : Type*} [Group G] [Group B]

theorem eq_top_of_map_eq_top_of_central_derived_kernel
    (f : G →* B) (hcentral : f.ker ≤ center G)
    (hderived : f.ker ≤ _root_.commutator G)
    (A : Subgroup G) (hA : A.map f = ⊤) : A = ⊤ := by
  have hs : A ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hA, comap_top]
  have hd : _root_.commutator G = ⁅A, A⁆ := by
    exact commutator_eq_of_central_supplement hs
      (hcentral.trans (by rw [coe_top, centralizer_univ]))
  have hk : f.ker ≤ A := hderived.trans (hd.le.trans
    (le_normalizer_iff_commutator_le_left.mp A.le_normalizer))
  rwa [sup_of_le_left hk] at hs

theorem center_subgroupOf_sylow_le_commutator
    [Finite G] [Group.IsPerfect G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (center G).subgroupOf P ≤ _root_.commutator P := by
  intro x hx
  have hm := center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨hx, Group.IsPerfect.mem_commutator⟩, x.property⟩
  rw [← map_subtype_commutator] at hm
  obtain ⟨w, hw, he⟩ := hm
  exact (Subtype.ext he : w = x) ▸ hw
end Subgroup
