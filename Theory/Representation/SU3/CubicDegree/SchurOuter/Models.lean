module

public import Theory.Representation.SU3.CubicDegree.SchurReduction
public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Scalars
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.GroupTheory.SolvableOuterQuotient


/-!
# The genuine adjoint model in the outer unitary argument

The model is the action of the full special unitary group on trace-zero
endomorphisms, through its literal determinant-one matrices. An adjoint Schur
model records an actual intertwiner after extending the original Schur field,
and the field degree s. In particular it has binary dimension 8s.

Two independent source steps are stated as explicit contracts. Graph stability
and the tensor estimates must construct this model for an outer 2F actor.
The adjoint calculation must give its fixed-space bounds, including s=2.
Neither contract is asserted here. The owning SchurOuter task assembles their
proofs and retains both as obligations until they are supplied.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32; Aschbacher--Smith K.3.3, printed p.456.
-/

public section

open Representation Representation.FrobeniusTensor
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Representation.SU3.CubicDegree.SchurOuter
variable {F K : Type*} [Field F] [Field K]

private def toSpecialLinear (J : HermitianForm 3 F) : J.specialSubgroup →* SL(3,F) where
  toFun g := ⟨g.val.val, congrArg Units.val ((J.mem_specialSubgroup_iff g.val).mp g.property).2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- Conjugation on the actual trace-zero endomorphisms. -/
noncomputable def adjoint (J : HermitianForm 3 F) (ι : F →+* K) :
    Representation K J.specialSubgroup (SL3.BinaryDefiningFactors.AdjointSpace K) :=
  (SL3.BinaryDefiningFactors.factorRep ι .adjoint).comp (toSpecialLinear J)

/-- The adjoint action is literal matrix conjugation, in the chosen embedding. -/
theorem adjoint_apply (J : HermitianForm 3 F) (ι : F →+* K)
    (g : J.specialSubgroup) (X : SL3.BinaryDefiningFactors.AdjointSpace K) :
    (adjoint J ι g X : Module.End K (Fin 3 → K)) =
      Matrix.toLin' (g.val.val.map ι) * X.val *
        Matrix.toLin' ((g⁻¹).val.val.map ι) := by
  change SL3.BinaryDefiningFactors.natural ι (toSpecialLinear J g) * X.val *
    SL3.BinaryDefiningFactors.natural ι ((toSpecialLinear J g)⁻¹) = _
  rw [← map_inv]
  rfl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- An actual absolute adjoint intertwiner over a Schur field of degree s. -/
structure AdjointSchurModel (s : ℕ) : Prop where
  fieldDegree : Module.finrank (ZMod 2) (SchurField σ) = s
  model : ∃ ι : F →+* Closure σ, Nonempty ((absoluteRep σ).Equiv (adjoint J ι))

/-- The binary dimension of the specified adjoint Schur model. -/
theorem AdjointSchurModel.finrank {s : ℕ} (h : AdjointSchurModel J σ s) :
    Module.finrank (ZMod 2) V = 8 * s := by
  obtain ⟨ι, ⟨e⟩⟩ := h.model
  have hd := e.toLinearEquiv.finrank_eq
  rw [SL3.BinaryDefiningFactors.finrank_adjointSpace] at hd
  rw [binary_finrank_eq σ, h.fieldDegree, hd, Nat.mul_comm]

open Representation.BinaryOffender

/-- The graph-stability step, including the exclusion of multiple tensor factors.
This contract is not a representation-classification theorem. -/
@[expose] def GraphStableReduction (s : ℕ) : Prop :=
  ∀ (A : Subgroup (linearNormalizer σ)), IsElementaryTwo A →
    IsCubic (normalizerRepresentation σ) A →
    fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
    (∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t) →
    ∀ t ∈ A, (actionImage σ).normalizerMonoidHom t ∉
      MulAut.innerSubgroup (actionImage σ) → AdjointSchurModel J σ s

/-- The model calculation. The second bound keeps the small-field endpoint
explicit; it is only needed when an actor has rank at least two. -/
@[expose] def AdjointFixedSpaceBounds (s : ℕ) : Prop :=
  AdjointSchurModel J σ s →
    ∀ (A : Subgroup (linearNormalizer σ)), IsElementaryTwo A →
      (∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t) →
      ∀ t ∈ A, (actionImage σ).normalizerMonoidHom t ∉
        MulAut.innerSubgroup (actionImage σ) →
        3 * s ≤ fixedCodim (normalizerRepresentation σ) A ∧
          (s = 2 → 2 ≤ rank A → 8 ≤ fixedCodim (normalizerRepresentation σ) A)

end Representation.SU3.CubicDegree.SchurOuter
