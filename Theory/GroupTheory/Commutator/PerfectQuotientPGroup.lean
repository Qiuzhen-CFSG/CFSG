module

public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Abelianization of an extension with perfect quotient

If a group surjects onto a perfect group with p-group kernel, its
abelianization is a p-group. The kernel and the derived subgroup generate
the whole group, so the kernel surjects onto the abelianization.

This is the elementary perfectness reduction in the central-cover step of
GLS, Volume 4, Chapter 2, Lemma 15.7: a group with full two-residual and
such a quotient is perfect. No centrality of the kernel is needed here.
-/

open Subgroup

namespace CentralExtension

/-- A p-group kernel surjects onto the abelianization when the quotient is perfect. -/
public theorem abelianization_isPGroup_of_perfect_quotient
    {E B : Type*} [Group E] [Group B] [Group.IsPerfect B]
    {p : ℕ} (f : E →* B) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) : IsPGroup p (E ⧸ commutator E) := by
  let q := QuotientGroup.mk' (commutator E)
  apply hker.of_surjective (q.comp f.ker.subtype)
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator E) y
  have hx : x ∈ f.ker ⊔ commutator E := by
    rw [ker_sup_commutator_eq_top_of_surjective f hf]
    trivial
  obtain ⟨k, hk, d, hd, rfl⟩ := mem_sup_of_normal_right.mp hx
  refine ⟨⟨k, hk⟩, ?_⟩
  change q k = q (k * d)
  rw [map_mul, show q d = 1 from (QuotientGroup.eq_one_iff d).mpr hd, mul_one]

end CentralExtension
