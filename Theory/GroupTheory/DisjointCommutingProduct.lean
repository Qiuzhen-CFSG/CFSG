module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Multiplication equivalence for disjoint commuting subgroups

Multiplication identifies the external direct product of two disjoint,
commuting subgroups with their join. The evaluation formula retains the
specified embeddings of both factors.

The proof restricts the noncommutative coproduct homomorphism to its range;
trivial intersection supplies injectivity. This is the internal direct product
criterion used in Aschbacher--Smith, I.7.4--I.7.5, printed p.426.
-/

namespace Subgroup

/-- The internal direct product, with multiplication as the isomorphism. -/
public theorem exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    {G : Type*} [Group G] (A B : Subgroup G)
    (hdisj : Disjoint A B) (hcomm : A ≤ centralizer (B : Set G)) :
    ∃ e : A × B ≃* ↥(A ⊔ B), ∀ a b, (e (a, b) : G) = (a : G) * (b : G) := by
  have hc : ∀ a : A, ∀ b : B, Commute (a : G) (b : G) := by
    intro a b
    exact (hcomm a.property b b.property).symm
  let f : A × B →* G := A.subtype.noncommCoprod B.subtype hc
  have hfr : f.range = A ⊔ B := by
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype hc).trans
      (by rw [range_subtype, range_subtype])
  let g : A × B →* ↥(A ⊔ B) := f.codRestrict _ (fun x => hfr ▸ ⟨x, rfl⟩)
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      exact mul_injective_of_disjoint hdisj (congrArg Subtype.val hxy)
    · intro c
      obtain ⟨x, hx⟩ := (show (c : G) ∈ f.range from hfr.symm ▸ c.property)
      exact ⟨x, Subtype.ext hx⟩
  exact ⟨MulEquiv.ofBijective g hg, fun _ _ => rfl⟩

end Subgroup
