/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.Representation.RepEquiv

/-!
# Isaacs Definition 1.12

The homogeneous component `M(V)` from Isaacs, *Character Theory of Finite
Groups*, Definition 1.12: the sum of all submodules of `V` isomorphic to `M`.
-/

noncomputable section

namespace BenderSuzuki
namespace External
namespace Isaacs
namespace I

/-- Isaacs, Definition 1.12: the `M`-homogeneous part of `V`. -/
@[expose] public def homogeneousComponent
    (A V M : Type*) [Semiring A]
    [AddCommMonoid V] [Module A V]
    [AddCommMonoid M] [Module A M] : Submodule A V :=
  sSup {W : Submodule A V | Nonempty (W ≃ₗ[A] M)}

end I
end Isaacs
end External
end BenderSuzuki
