module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Sylow centers above a self-centralizing p-core

When the center of the p-core is central in the whole group, the center
of every Sylow p-subgroup is exactly that core center. The proof uses
containment of the core in the chosen Sylow and its centralizer bound.
All centers keep their original subgroup embeddings.

Source application: Aschbacher–Smith 5.2.2, printed pp.647–648, for the
binary-triality arms parabolic.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- When the center of the self-centralizing p-core is central, it is the
center of each Sylow subgroup, with the original embeddings retained. -/
theorem mapped_sylow_center_eq_core_center {p : ℕ} [Fact p.Prime]
    (S : Sylow p G)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (hz : (center (pCore p G)).map (pCore p G).subtype ≤ center G) :
    (center S).map (S : Subgroup G).subtype =
      (center (pCore p G)).map (pCore p G).subtype := by
  have hQS : pCore p G ≤ S := pCore_isPGroup.le_sylow_of_normal S
  apply le_antisymm
  · rintro z ⟨s,hs,rfl⟩
    have hsC : (s : G) ∈ centralizer (pCore p G : Set G) := by
      intro q hq
      exact congrArg Subtype.val (mem_center_iff.mp hs ⟨q,hQS hq⟩)
    refine ⟨⟨s,hc hsC⟩,mem_center_iff.mpr ?_,rfl⟩
    intro q
    exact Subtype.ext (hsC q q.property)
  · rintro z ⟨q,hq,rfl⟩
    refine ⟨⟨q,hQS q.property⟩,mem_center_iff.mpr ?_,rfl⟩
    intro s
    exact Subtype.ext (mem_center_iff.mp (hz (mem_map_of_mem _ hq)) s)
end Subgroup
