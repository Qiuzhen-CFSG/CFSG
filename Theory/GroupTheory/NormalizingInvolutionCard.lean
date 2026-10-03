module
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic

/-!
# Adjoining an external normalizing involution

If w is an involution outside a subgroup H and normalizes H, then adjoining
w doubles the cardinality of H. No cyclicity or ambient finiteness is
required: the actual multiplication map H × zpowers(w) onto the join is
a bijection, so the natural-cardinality identity holds in all cases.

The two powers of w and the outside condition make the factors disjoint.
The normalizer condition identifies their set product with the generated
subgroup. This supplies a shared counting step for the diagonal monomial
and quadratic-torus matrix models in ABG II.2 Lemma1, article p17.
-/

namespace Subgroup
open scoped Pointwise

public theorem card_sup_zpowers_of_normalizing_involution
    {G : Type*} [Group G] (H : Subgroup G) (w : G)
    (hw : w ^ 2 = 1) (hout : w ∉ H) (hnorm : w ∈ normalizer H) :
    Nat.card (H ⊔ zpowers w : Subgroup G) = 2 * Nat.card H := by
  classical
  have hwne : w ≠ 1 := fun h => hout (h ▸ H.one_mem)
  have hworder : orderOf w = 2 := orderOf_eq_prime hw hwne
  have hfin : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hw⟩
  have hcases {x : G} (hx : x ∈ zpowers w) : x = 1 ∨ x = w := by
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, hworder] at hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    have hi2 := Finset.mem_range.mp hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact Or.inl (by simpa using hix.symm)
    · exact Or.inr (by simpa using hix.symm)
  have hdisj : Disjoint H (zpowers w) := disjoint_def.mpr (by
    intro x hxH hxw
    rcases hcases hxw with rfl | rfl
    · rfl
    · exact (hout hxH).elim)
  let S := H ⊔ zpowers w
  let f : H × zpowers w → S := fun a => ⟨a.1 * a.2, mul_mem_sup a.1.property a.2.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact mul_injective_of_disjoint hdisj (congrArg Subtype.val hab)
    · intro g
      have hg : (g : G) ∈ (H : Set G) * (zpowers w : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left H (zpowers w) (zpowers_le.mpr hnorm)]
        exact g.property
      obtain ⟨a, ha, b, hb, hab⟩ := hg
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, Nat.card_zpowers, hworder] at hc
  simpa [Nat.mul_comm, S] using hc.symm

end Subgroup

