module

public import Theory.GroupTheory.SubgroupEnumeration
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Finite membership certificates for generated subgroups

A predicate containing the identity and stable under right multiplication by
all generators and their inverses contains the generated subgroup. Conversely,
explicit generator words for its elements prove that it contains no extra
points. This reduces finite subgroup membership tables to short word and
transition checks, without testing every pair of elements.

Source: subgroup closure induction and evaluation of generator words.
-/

namespace Theory.GroupTheory.SubgroupEnumeration

/-- Word witnesses and generator transitions certify an exact membership predicate. -/
public theorem mem_closure_range_iff_of_word_certificate {G : Type*} [Group G]
    {n : Nat} (s : Fin n → G) (P : G → Prop) (word : G → List (Fin n))
    (h1 : P 1)
    (hm : ∀ x, P x → ∀ i, P (x * s i))
    (hi : ∀ x, P x → ∀ i, P (x * (s i)⁻¹))
    (hw : ∀ x, P x → evalWord s (word x) = x) (x : G) :
    x ∈ Subgroup.closure (Set.range s) ↔ P x := by
  constructor
  · intro hx
    apply Subgroup.closure_induction_right (p := fun x _ => P x) h1 _ _ hx
    · rintro y _ _ ⟨i, rfl⟩ hy
      exact hm y hy i
    · rintro y _ _ ⟨i, rfl⟩ hy
      exact hi y hy i
  · intro hx
    rw [← hw x hx]
    exact evalWord_mem s (Subgroup.closure (Set.range s)) (fun i => Subgroup.subset_closure ⟨i, rfl⟩) _

end Theory.GroupTheory.SubgroupEnumeration
