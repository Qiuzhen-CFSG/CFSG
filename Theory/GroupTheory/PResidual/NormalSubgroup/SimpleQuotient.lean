module

public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Normal p-perfect subgroups over a simple quotient

If a p-perfect group has a normal p-subgroup with simple quotient, each
nontrivial normal p-perfect subgroup is the whole group. Its image in the
simple quotient is either trivial, which makes it a p-group, or surjective,
which makes its ambient quotient a p-group. P-perfectness excludes both
proper cases.

This is the residual argument behind equality of the two actor projections
in Aschbacher--Smith, 15.3.39, printed pp.1137--1138.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- A nontrivial normal p-perfect subgroup fills a p-perfect group with
simple quotient by a normal p-subgroup. -/
public theorem eq_top_of_normal_isPPerfect_of_simple_quotient {p : ℕ} (Q : Subgroup G) [Q.Normal]
    [IsSimpleGroup (G ⧸ Q)] (hQ : IsPGroup p Q) (hG : IsPPerfect p G)
    (N : Subgroup G) [N.Normal] (hN : IsPPerfect p N) (hne : N ≠ ⊥) : N = ⊤ := by
  let q := QuotientGroup.mk' Q
  have hnmap : (N.map q).Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective Q)
  rcases hnmap.eq_bot_or_eq_top with hz | ht
  · have hNQ : N ≤ Q := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz
    have hp : IsPGroup p N := hQ.to_le hNQ
    have hquot : IsPGroup p (N ⧸ (⊥ : Subgroup N)) :=
      hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _)
    have hbot : (⊥ : Subgroup N) = ⊤ := hN _ inferInstance hquot
    apply (hne _).elim
    apply le_bot_iff.mp
    intro x hx
    have hh : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := hbot.symm ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hh)
  · have hsup : N ⊔ Q = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨n, hn, he⟩ := mem_map.mp (show q x ∈ N.map q by rw [ht]; trivial)
      have hnx : n⁻¹ * x ∈ Q := QuotientGroup.eq.mp he
      have hh : n * (n⁻¹ * x) ∈ N ⊔ Q :=
        (N ⊔ Q).mul_mem ((le_sup_left : N ≤ N ⊔ Q) hn) ((le_sup_right : Q ≤ N ⊔ Q) hnx)
      simpa using hh
    exact hG N inferInstance (isPGroup_quotient_of_sup_eq_top N Q hQ hsup)


end Subgroup
