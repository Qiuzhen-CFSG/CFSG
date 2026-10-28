module

public import Theory.GroupTheory.TightlyEmbedded.ProductDisconnected
public import Theory.ElementaryAbelian.Basic

/-!
# Involution generation of an elementary normal closure

For an elementary abelian two-subgroup, the conjugacy closure of its
involutions generates its actual normal closure. Every nonidentity element
of the subgroup is an involution, and adjoining the identity adds no generator.
This identifies the two generated subgroups in Aschbacher--Smith I.8.2--I.8.3,
printed pp.429--430, without changing their subsequent quotient maps.
-/

namespace Theory.GroupTheory
open Subgroup BenderSuzuki
variable {G : Type*} [Group G]

/-- The involution-generated subgroup in I.8.2 is the actual normal closure
when the original subgroup is elementary abelian of exponent two. -/
public theorem involutionConjugates_closure_eq_normalClosure
    (V : Subgroup G) [IsElementaryAbelian 2 V] :
    closure (involutionConjugates V) = normalClosure (V : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro z ⟨g, v, hv, _hi, rfl⟩
    exact (inferInstance : (normalClosure (V : Set G)).Normal).conj_mem
      v (subset_normalClosure hv) g
  · rw [normalClosure, closure_le]
    intro z hz
    obtain ⟨v, hv, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨g, rfl⟩ := isConj_iff.mp hc
    by_cases hne : v = 1
    · simp [hne]
    · exact subset_closure ⟨g, v, hv,
        ⟨hne, elemPow_eq_one_of_isElementaryAbelian v hv⟩, rfl⟩

end Theory.GroupTheory
