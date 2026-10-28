module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.Mathieu.M22.Properties.Automorphisms

/-!
# From M₂₂ automorphism coverage to the outer restriction

The full hexad-design group contains the actual M₂₂ as a normal subgroup
of index two. Its conjugation map therefore induces a map from that concrete
quotient to Out(M₂₂). Surjectivity of conjugation on all automorphisms makes
this quotient map surjective and proves the required two-group restriction.

Coverage is an explicit premise: the already established injectivity of
`m22DesignAutToAut` does not suffice. Source: GLS3, Table 5.3c, and the
outer-group inspection on printed p.510 of Aschbacher–Smith, combined
1 March 2004 manuscript.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory Sporadic.Mathieu

/-- Full automorphism coverage makes the concrete order-two quotient cover Out(M₂₂). -/
theorem m22_outer_isPGroup_two_of_coverage
    (hcover : Function.Surjective m22DesignAutToAut) :
    IsPGroup 2 (MulAut.Outer M22) := by
  let N := M22.subgroupOf m22DesignAut
  let : N.Normal := M22_normal_in_m22DesignAut
  have hle : N ≤ (MulAut.innerSubgroup M22).comap m22DesignAutToAut := by
    intro g hg
    refine ⟨⟨g.val, hg⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm]
    rfl
  let q : (m22DesignAut ⧸ N) →* MulAut.Outer M22 :=
    QuotientGroup.map N (MulAut.innerSubgroup M22) m22DesignAutToAut hle
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M22) x
    obtain ⟨g, rfl⟩ := hcover a
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have htwo : IsPGroup 2 (m22DesignAut ⧸ N) :=
    IsPGroup.of_card (n := 1) (by
      rw [← N.index_eq_card]
      have heq : N = m22EvenDesignAut := by
        ext g
        simp [N, M22, m22EvenDesignAut]
      rw [heq, m22EvenDesignAut_index]
      rfl)
  exact htwo.of_surjective q hq

/-- Transport of the conditional M₂₂ calculation through the actual model equivalence. -/
theorem m22_model_outer_cyclicNormalOddQuotient_of_coverage
    {S : Type*} [Group S] (e : S ≃* M22)
    (hcover : Function.Surjective m22DesignAutToAut) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  exact (hasCyclicNormalOddQuotient_of_isPGroup_two
    (m22_outer_isPGroup_two_of_coverage hcover)).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
