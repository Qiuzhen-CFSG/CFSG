module

public import Theory.AlgebraicGroup.Bor1.GeometricQuotientDescent

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false in
public theorem theorem_1_1_2_b
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : H.toSubgroup.Normal) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (π : AlgebraicGroup.Morphism G Q),
      Function.Surjective π.onPoints ∧
        π.kernel = H.toSubgroup ∧
      ∀ {I : Variety k} (_ : AlgebraicGroup I)
          (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
          ∃! ψ : AlgebraicGroup.Morphism Q I, ψ.comp π = φ := by
  let D := Bor1.theorem_1_1_2_b_quotientData H hH
  letI : AlgebraicGroup D.quotient := D.quotientAlgebraicGroup
  refine ⟨D.quotient, D.quotientAlgebraicGroup, D.projection,
    D.pointSurjective, D.kernel_eq, ?_⟩
  intro I hI φ hφ
  exact D.algebraicUniversal φ hφ

end Theory.AlgebraicGroup
