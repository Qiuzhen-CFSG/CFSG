module

public import Theory.AlgebraicGroup.Bor1.TangentVanishingIdeal
public import Theory.AlgebraicGroup.RightTranslation.Vanishing

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An identity tangent vector comes from a closed subgroup as soon as it
annihilates the fixed finite generating family of the vanishing ideal. -/
public theorem identityTangent_mem_range_of_vanishingIdealGenerator_zero
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (D : IdentityPointDerivation G)
    (hD : ∀ i : H.vanishingIdealGeneratorData.generators, D i.1 = 0) :
    D ∈ LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  let J : Ideal G.PolynomialFunction := {
    carrier := {f | f ∈ H.vanishingIdeal ∧ D f = 0}
    zero_mem' := ⟨H.vanishingIdeal.zero_mem, map_zero D⟩
    add_mem' := by
      intro f g hf hg
      exact ⟨H.vanishingIdeal.add_mem hf.1 hg.1,
        by rw [map_add, hf.2, hg.2, add_zero]⟩
    smul_mem' := by
      intro a f hf
      refine ⟨H.vanishingIdeal.mul_mem_left a hf.1, ?_⟩
      change D (a * f) = 0
      rw [D.leibniz, hf.2]
      have hfeval : f 1 = 0 :=
        (H.mem_vanishingIdeal_iff f).mp hf.1 1 H.toSubgroup.one_mem
      change a 1 * 0 + f 1 * D a = 0
      rw [hfeval]
      simp }
  apply (identityTangent_inclusion_range_iff_vanishingIdeal H D).mpr
  intro f hf
  have hfspan : f ∈ Ideal.span
      (H.vanishingIdealGeneratorData.generators : Set G.PolynomialFunction) := by
    rw [H.vanishingIdealGeneratorData.span_eq]
    exact hf
  have hspan : Ideal.span
      (H.vanishingIdealGeneratorData.generators : Set G.PolynomialFunction) ≤ J := by
    apply Ideal.span_le.mpr
    intro q hq
    let i : H.vanishingIdealGeneratorData.generators := ⟨q, hq⟩
    exact ⟨H.generator_mem_vanishingIdeal i, hD i⟩
  exact (hspan hfspan).2

end Theory.AlgebraicGroup.Bor1
