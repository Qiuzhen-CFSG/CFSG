module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# p-cores in overgroups of a Sylow subgroup

An overgroup of a Sylow p-subgroup contains the ambient p-core, and its
intrinsic p-core contains that core. The self-centralizing property of the
ambient p-core consequently passes to the overgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.6
(stated there for p = 2).
-/

namespace Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- An overgroup of a Sylow p-subgroup contains the ambient p-core in its
own p-core. -/
public theorem pCore_le_map_of_sylow_le (T : Sylow p G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) :
    pCore p G ≤ (pCore p H).map H.subtype := by
  have hcoreH : pCore p G ≤ H := (pCore_isPGroup.le_sylow_of_normal T).trans hTH
  have h : (pCore p G).subgroupOf H ≤ pCore p H :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  simpa only [map_subgroupOf_eq_of_le hcoreH] using map_mono (f := H.subtype) h

/-- Self-centralizing p-cores pass to overgroups of Sylow p-subgroups. -/
public theorem centralizer_pCore_le_of_sylow_le (T : Sylow p G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hG : centralizer (pCore p G : Set G) ≤ pCore p G) :
    centralizer (pCore p H : Set H) ≤ pCore p H := by
  have hcore := pCore_le_map_of_sylow_le T H hTH
  intro x hx
  have hxG : (x : G) ∈ centralizer (pCore p G : Set G) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hcore hy
    exact congrArg H.subtype (hx z hz)
  obtain ⟨z, hz, hzx⟩ := hcore (hG hxG)
  exact H.subtype_injective hzx ▸ hz

end Subgroup
