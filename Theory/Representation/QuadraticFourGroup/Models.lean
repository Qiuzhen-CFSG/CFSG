module

public import Theory.Representation.QuadraticFourGroup.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Concrete outputs for quadratic four-group classification

The quotient in GLS2 Theorem 25.14 is the quotient by the intrinsic two-core
of the actual component orbit. `TwoFactorModel` specifies a multiplicative
equivalence to two concrete projective special linear groups. Its projection
is the composite of that equivalence with the actual quotient map; we prove
surjectivity and its exact kernel.

`IsNaturalTensorAlong` specifies the module conclusion via an equivariant
linear equivalence. Each factor is a faithful representation on the literal
two-dimensional coordinate space over `GaloisField 2 n`, and the tensor is
taken over that field before restricting scalars to `ZMod 2`. This permits
the natural-module twists allowed by the source remarks. These are output
definitions, not assumed recognition theorems.
-/

@[expose] public section

open scoped MatrixGroups TensorProduct

namespace Representation.QuadraticFourGroup

/-- The concrete group appearing in each factor of the source conclusion. -/
abbrev Factor (n : ℕ) := PSL(2, GaloisField 2 n)

/-- A model of the actual quotient, retaining the strict source parameter bound. -/
structure TwoFactorModel (E : Type*) [Group E] where
  n : ℕ
  one_lt : 1 < n
  quotientEquiv : E ⧸ pCore 2 E ≃* Factor n × Factor n

namespace TwoFactorModel

variable {E : Type*} [Group E] (M : TwoFactorModel E)

/-- The compatible map from the original group to the two concrete factors. -/
noncomputable def projection : E →* Factor M.n × Factor M.n :=
  M.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 E))

theorem projection_surjective : Function.Surjective M.projection :=
  M.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The model projection kills exactly the two-core, not an arbitrary residual. -/
theorem ker_projection : M.projection.ker = pCore 2 E := by
  ext x
  change M.quotientEquiv (QuotientGroup.mk' (pCore 2 E) x) = 1 ↔ _
  rw [map_eq_one_iff M.quotientEquiv M.quotientEquiv.injective]
  exact QuotientGroup.eq_one_iff x

end TwoFactorModel

/-- The literal two-dimensional vector space for one natural factor. -/
abbrev NaturalSpace (n : ℕ) := Fin 2 → GaloisField 2 n

/-- The tensor product is over the extension field, not over the prime field. -/
abbrev TensorSpace (n : ℕ) :=
  NaturalSpace n ⊗[GaloisField 2 n] NaturalSpace n

/-- The external tensor action, with scalars restricted to the binary field. -/
noncomputable def binaryTensor {n : ℕ}
    (τ₁ τ₂ : Representation (GaloisField 2 n) (Factor n) (NaturalSpace n)) :
    Representation (ZMod 2) (Factor n × Factor n) (TensorSpace n) where
  toFun g := (TensorProduct.map (τ₁ g.1) (τ₂ g.2)).restrictScalars (ZMod 2)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [Module.End.mul_eq_comp, TensorProduct.map_comp]

/-- A genuine equivariant tensor identification, inflated along a specified
map from the original acting group. The coordinate spaces have dimension two
over the extension field and both natural actions must be faithful. -/
def IsNaturalTensorAlong {E W : Type*} [Group E]
    [AddCommGroup W] [Module (ZMod 2) W] {n : ℕ}
    (π : E →* Factor n × Factor n) (σ : Representation (ZMod 2) E W) : Prop :=
  ∃ τ₁ τ₂ : Representation (GaloisField 2 n) (Factor n) (NaturalSpace n),
    Function.Injective τ₁ ∧ Function.Injective τ₂ ∧
      Nonempty (σ.Equiv ((binaryTensor τ₁ τ₂).comp π))

end Representation.QuadraticFourGroup

end
