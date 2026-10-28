module

public import Theory.AlgebraicGroup.Bor1.TangentGeneratorCriterion

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An infinitesimal operator on Chevalley's right-translation space which
preserves the distinguished vanishing subspace detects only tangent vectors
coming from the closed subgroup. -/
public theorem identityTangent_mem_range_of_infinitesimalChevalley_stable
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (D : IdentityPointDerivation G)
    (A : Module.End k H.rightTranslateVanishingSpan)
    (hEval : ∀ q : H.rightTranslateVanishingSpan, (A q).1 1 = D q.1)
    (hStable : ∀ q : H.rightTranslateVanishingSpan,
      q.1 ∈ H.rightTranslateVanishingSubspace →
        (A q).1 ∈ H.rightTranslateVanishingSubspace) :
    D ∈ LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  apply identityTangent_mem_range_of_vanishingIdealGenerator_zero H D
  intro i
  let q : H.rightTranslateVanishingSpan :=
    ⟨i.1, H.generator_mem_rightTranslateVanishingSpan i⟩
  have hA := hStable q (H.generator_mem_rightTranslateVanishingSubspace i)
  have hzero : (A q).1 1 = 0 :=
    (H.mem_vanishingIdeal_iff (A q).1).mp hA.2 1 H.toSubgroup.one_mem
  rw [hEval q] at hzero
  exact hzero

end Theory.AlgebraicGroup.Bor1
