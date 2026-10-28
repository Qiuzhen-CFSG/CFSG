module
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Normal closure and the literal conjugating range

The normal closure of a subgroup is its conjugate span under the whole group.
After a homomorphism, the conjugating group is exactly the range of that map.
In particular an inclusion of a finite local group into an infinite completion
does not replace relative normal closure by ambient normal closure.

This comparison is used for the marked adjacent-core and Sylow-center
closures in DGS, *Groups and Graphs* (1985), 6.3--6.5, pp.120--122.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Normal closure is conjugate generation by the full original group. -/
theorem normalClosure_eq_conjugateSpanBy_top (A : Subgroup G) :
    normalClosure (A : Set G) = conjugateSpanBy A ⊤ := by
  let : (conjugateSpanBy A ⊤).Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (le_normalizer_conjugateSpanBy A ⊤))
  exact le_antisymm (normalClosure_le_normal (le_conjugateSpanBy A ⊤))
    (conjugateSpanBy_le le_normalClosure le_normalizer_of_normal)

/-- Under any homomorphism, the original conjugators have exactly its range. -/
theorem map_normalClosure_eq_conjugateSpanBy_range (A : Subgroup G) (f : G →* H) :
    (normalClosure (A : Set G)).map f = conjugateSpanBy (A.map f) f.range := by
  rw [normalClosure_eq_conjugateSpanBy_top, map_conjugateSpanBy, ← MonoidHom.range_eq_map]

end Subgroup
