module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Basis
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Descent

/-!
# Apply the checked degree-160 inverse to the carrier construction

The explicit inverse-basis check supplies the `P * Pi = 1` premise in the
rank-one density argument for the saved degree-160 candidate. The generator
relations, rank-one element, literal orbit identities and right inverse remain
explicit numerical obligations; presentation injectivity is the independent
earlier-source input. This proves a conditional construction step, not existence
of the degree-160 model.

Source data and conventions: `LargeModels/source/README.md`.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Basis
open Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization
variable {F : Type*} [Field F] [CharP F 2]

/-- The saved ATLAS orbit basis has the required left inverse. Its numerical
inverse premise is discharged, while the remaining source identities stay visible. -/
theorem action_absolutelyIrreducible
    (hp : Function.Injective Presentation.toCarrier)
    (A B : (Matrix (Fin 160) (Fin 160) F)ˣ) (h : Presentation.Relations A B)
    (v lam : Fin 160 → F) (Q Qi : Matrix (Fin 160) (Fin 160) F)
    (he : Matrix.vecMulVec v lam ∈
      Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin 160) (Fin 160) F)))
    (hl : ∀ i, ∃ W ∈ Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin 160) (Fin 160) F)),
      W.mulVec v = fun k => Binary.eval F 160 leftBasis k i)
    (hr : ∀ j, ∃ W ∈ Algebra.adjoin F ({↑A, ↑B} : Set (Matrix (Fin 160) (Fin 160) F)),
      Matrix.vecMul lam W = Q j)
    (hQ : Qi * Q = 1) : IsAbsolutelyIrreducible (action hp A B h) :=
  action_absolutelyIrreducible_of_rankOne hp A B h v lam
    (Binary.eval F 160 leftBasis) (Binary.eval F 160 leftInverse) Q Qi
    he hl hr (left_basis_mul_inverse F) hQ

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Basis
