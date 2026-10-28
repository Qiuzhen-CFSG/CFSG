module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.PGroup

/-!
# Lifting prime-power fixed subgroups

For a compatible homomorphism with p-group kernel, a p-group fixed
subgroup downstairs implies a p-group fixed subgroup upstairs. The latter
embeds in the full preimage of the former; surjectivity on fixed points
is unnecessary. This applies in particular to central covers.

Source: the central-cover step in Aschbacher–Smith 16.4.8, combined
manuscript of 1 March 2004, printed p.1188.
-/

namespace MulAut

/-- Fixed points in a p-group extension form a p-group if their images do. -/
public theorem isPGroup_fixedSubgroup_of_compatible
    {G H : Type*} [Group G] [Group H] {p : ℕ}
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hker : IsPGroup p f.ker) (heq : ∀ x, f (a x) = b (f x))
    (hb : IsPGroup p b.fixedSubgroup) : IsPGroup p a.fixedSubgroup := by
  apply (hb.comap_of_ker_isPGroup f hker).to_le
  intro x hx
  change f x ∈ b.fixedSubgroup
  rw [mem_fixedSubgroup, ← heq, (mem_fixedSubgroup _ _).mp hx]

end MulAut
