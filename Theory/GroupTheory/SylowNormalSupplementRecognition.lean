module
public import Mathlib.GroupTheory.Sylow

/-!
# Recognizing a Sylow subgroup in a normal supplement

A p-subgroup supplementing a normal subgroup C is Sylow if it contains
a Sylow subgroup of C. Extend it to T and use maximality inside C to
identify T∩C. The product C R=G then forces every element of T into R.

Source application: Aschbacher–Smith C.2.7, printed p.146.
-/

public section
open Subgroup
namespace Subgroup

theorem exists_sylow_eq_of_normal_supplement {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (C R : Subgroup G) [C.Normal] (hR : IsPGroup p R)
    (hgen : C ⊔ R = ⊤) (S : Sylow p C)
    (hSR : (S : Subgroup C).map C.subtype ≤ R) :
    ∃ T : Sylow p G, (T : Subgroup G) = R := by
  obtain ⟨T,hRT⟩ := hR.exists_le_sylow
  have hST : (S : Subgroup C) ≤ (T : Subgroup G).subgroupOf C :=
    map_le_iff_le_comap.mp (hSR.trans hRT)
  have he : (T : Subgroup G).subgroupOf C = (S : Subgroup C) :=
    S.is_maximal' T.isPGroup'.comap_subtype hST
  refine ⟨T,le_antisymm ?_ hRT⟩
  intro t ht
  obtain ⟨c,hc,r,hr,hcr⟩ := mem_sup_of_normal_left.mp (hgen.ge (mem_top t))
  have hcT : c ∈ (T : Subgroup G) := by
    have hh := T.mul_mem ht (T.inv_mem (hRT hr))
    rwa [←hcr,mul_inv_cancel_right] at hh
  have hcS : (⟨c,hc⟩ : C) ∈ (S : Subgroup C) := he ▸ hcT
  rw [←hcr]
  exact R.mul_mem (hSR (mem_map.mpr ⟨⟨c,hc⟩,hcS,rfl⟩)) hr

end Subgroup
