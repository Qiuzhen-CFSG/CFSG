module

public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover

/-!
# Transport of normal quasisimple subgroups of index two

A group isomorphism carries the subgroup itself, its normality, its index,
and its center to the corresponding data in the target group. This allows
an actual representative centralizer calculation to be used on all its
isomorphic copies, including the involution centralizers of GLS3 Table 5.3p.
-/

public section

open Subgroup
namespace Theory.GroupTheory

variable {G H : Type*} [Group G] [Group H] {z : ℕ}

/-- Transport the witness through an actual group isomorphism. -/
theorem HasQuasisimpleNormalOfIndexTwo.of_mulEquiv
    (h : HasQuasisimpleNormalOfIndexTwo G z) (e : G ≃* H) :
    HasQuasisimpleNormalOfIndexTwo H z := by
  obtain ⟨L, hn, hq, hi, hz⟩ := h
  let : L.Normal := hn
  let : IsQuasisimple L := hq
  refine ⟨L.map e.toMonoidHom, hn.map _ e.surjective,
    IsQuasisimple.of_mulEquiv (e.subgroupMap L), ?_, ?_⟩
  · exact (L.index_map_equiv e).trans hi
  · exact (Nat.card_congr (centerCongr (e.subgroupMap L)).toEquiv).symm.trans hz

end Theory.GroupTheory
