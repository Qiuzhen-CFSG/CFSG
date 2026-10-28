module

public import Theory.GroupTheory.CComponent.Basic

/-!
# The local C-component family

Definition A.3.10 associates to a Sylow 2-subgroup `T` the subgroups `B` that
are C-components of `⟨B, T⟩`. The definition and the restriction argument in
A.3.11 work for arbitrary `T`, without quasithin or finiteness assumptions.
The later classification of this family requires the source's full hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition A.3.10 and Lemma A.3.11, p. 46.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterA.Section03

variable {G : Type*} [Group G]

/-- A.3.10: the C-components of the subgroups generated with `T`, viewed in `G`. -/
def localCComponents (T : Subgroup G) : Set (Subgroup G) :=
  {B | (B.subgroupOf (B ⊔ T)).IsCComponent}

/-- A.3.11: a C-component of an overgroup of `T` belongs to the local family. -/
theorem cComponent_mem_localCComponents {B H T : Subgroup G}
    (hB : (B.subgroupOf H).IsCComponent) (hBH : B ≤ H) (hTH : T ≤ H) :
    B ∈ localCComponents T :=
  hB.subgroupOf_of_le le_sup_left (sup_le hBH hTH)

/-- Every ambient C-component belongs to the local family. -/
theorem isCComponent_mem_localCComponents {B T : Subgroup G} (hB : B.IsCComponent) :
    B ∈ localCComponents T :=
  hB.subgroupOf le_sup_left

/-- Shrinking `T` preserves membership in the local C-component family. -/
theorem localCComponents_antitone : Antitone (localCComponents (G := G)) := by
  intro S T hST B hB
  exact hB.subgroupOf_of_le le_sup_left (sup_le_sup_left hST B)

end CFSG.Quasithin.ChapterA.Section03
