module

public import Theory.AlgebraicGroup.Jordan.Basic

universe u

/-! Local finiteness of the affine right-translation action. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Right translation on the polynomial-function algebra is locally finite. -/
public theorem rightTranslationPullback_locallyFinite
    (G : Variety k) [AlgebraicGroup G]
    (g : Variety.Point G) (f : Variety.PolynomialFunction G) :
    ∃ P : Submodule k (Variety.PolynomialFunction G),
      Module.Finite k P ∧
      P ∈ Module.End.invtSubmodule (rightTranslationPullback G g) ∧
      f ∈ P := by
  let P := AlgebraicGroup.rightTranslateOrbitSpan G f
  refine ⟨P, inferInstance, ?_, ?_⟩
  · rw [Module.End.mem_invtSubmodule]
    intro q hq
    exact AlgebraicGroup.rightTranslateOrbitSpan_stable G f g q hq
  · have hone : rightTranslationPullback G (1 : Variety.Point G) f = f := by
      rw [rightTranslationPullback_one]
      rfl
    rw [← hone]
    exact Submodule.subset_span ⟨1, rfl⟩

end Theory.AlgebraicGroup
