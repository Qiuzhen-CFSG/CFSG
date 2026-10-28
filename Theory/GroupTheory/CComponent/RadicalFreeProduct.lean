module

public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Direct products from radical-free components

The intersection of a component with a subgroup centralizing it lies in the
component's center. In a finite group with trivial solvable radical this center
is trivial. Multiplication therefore identifies the external direct product
with the join, retaining the embeddings of both factors.

This is the internal direct-product consequence of Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.3.3(5)--(6), printed pp.42--43.
It asserts neither normality of the join in the ambient group nor that these
are its only components.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G] {L K : Subgroup G}

/-- A subgroup centralizing a component in a radical-free group meets it
trivially. Only the first factor needs to be a component. -/
theorem IsCComponent.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot
    (hL : L.IsCComponent) (hG : solvableRadical G = ⊥)
    (hc : ⁅L, K⁆ = ⊥) : Disjoint L K := by
  apply Subgroup.disjoint_def.mpr
  intro x hxL hxK
  have hz : (⟨x, hxL⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact ((commutator_eq_bot_iff_le_centralizer.mp hc y.property) x hxK).symm
  have hcenter := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hG hL.subnormal
  have hx : (⟨x, hxL⟩ : L) = 1 := mem_bot.mp (hcenter ▸ hz)
  exact congrArg (fun y : L => (y : G)) hx

/-- Multiplication supplies actual direct-product coordinates on the join. -/
theorem IsCComponent.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot
    (hL : L.IsCComponent) (hG : solvableRadical G = ⊥)
    (hc : ⁅L, K⁆ = ⊥) :
    ∃ e : L × K ≃* ↥(L ⊔ K), ∀ l k, (e (l, k) : G) = (l : G) * (k : G) :=
  exists_mulEquiv_prod_sup_of_disjoint_of_commuting L K
    (hL.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hG hc)
    (commutator_eq_bot_iff_le_centralizer.mp hc)

end Subgroup
