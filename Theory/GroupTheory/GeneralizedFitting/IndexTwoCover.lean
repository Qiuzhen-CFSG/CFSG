module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Components above a normal quasisimple subgroup of index two

Every perfect subgroup lies in a subgroup of index two. Consequently a
normal quasisimple subgroup of index two is the unique component. If its
center is nontrivial, no component can be isomorphic to a centerless group.
No splitting of the extension is used.

This is the component argument for the central covering groups in GLS3,
Table 5.3p (the Held involution centralizers).
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory

variable {G D : Type*} [Group G] [Group D]

/-- A normal quasisimple subgroup of index two is the only component. -/
theorem IsComponent.eq_of_index_two_quasisimple {K L : Subgroup G}
    (hK : IsComponent G K) [L.Normal] [IsQuasisimple L] (hi : L.index = 2) :
    K = L := by
  let : IsQuasisimple K := hK.2
  exact hK.eq_of_le ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
    (le_of_isPerfect_of_index_eq_two K L hi)

/-- The intrinsic information needed from an index-two covering extension.
The subgroup, its normality and its center are all inside the actual group. -/
def HasQuasisimpleNormalOfIndexTwo (G : Type*) [Group G] (z : ℕ) : Prop :=
  ∃ L : Subgroup G, L.Normal ∧ IsQuasisimple L ∧
    L.index = 2 ∧ Nat.card (center L) = z

/-- A component of an index-two quasisimple extension with nontrivial center
cannot be isomorphic to a centerless group. -/
theorem HasQuasisimpleNormalOfIndexTwo.not_component_equiv
    {z : ℕ} (h : HasQuasisimpleNormalOfIndexTwo G z) (hz : z ≠ 1)
    (hD : center D = ⊥) {K : Subgroup G} (hK : IsComponent G K) :
    ¬ Nonempty (K ≃* D) := by
  obtain ⟨L, hn, hq, hi, hc⟩ := h
  let : L.Normal := hn
  let : IsQuasisimple L := hq
  have hKL := hK.eq_of_index_two_quasisimple hi
  subst K
  rintro ⟨e⟩
  have he := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [hc, hD, Subgroup.card_bot] at he
  exact hz he

end Theory.GroupTheory
