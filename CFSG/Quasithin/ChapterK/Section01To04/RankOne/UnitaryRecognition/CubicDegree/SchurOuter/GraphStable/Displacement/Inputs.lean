module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Inputs
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.Rigidity

/-!
# The remaining outer tensor conjugation contract

The source must supply coordinates in which tensorwise transpose induces
exactly the same conjugation on the absolute component as the literal outer
actor. This is a matrix and perfect-central-quotient obligation, not a
numerical dimension hypothesis. Irreducibility and the two square-one equations
remove its scalar ambiguity in `TensorDisplacement.Rigidity`; the final
`GraphStable.Displacement` module owns the displacement assembly.

The separate input module lets the geometric producer and final assembly
share this contract without circular imports. Its construction must retain
arbitrary Hermitian forms, central kernels, every adjoint position, and s=2.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors Representation.BinaryOffender
open Representation.SU3.CubicDegree.SchurOuter
open Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- The remaining outer-to-tensor coordinate statement. It identifies the conjugation
induced on the actual absolute component, before removal of Schur scalar ambiguity. -/
@[expose] def OuterTensorConjugation (s : ℕ) : Prop :=
  ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
    Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)) →
    naturalCount w = 0 →
    ∀ (A : Subgroup (linearNormalizer σ)), IsElementaryTwo A →
      ∀ hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t,
        ∀ t : linearNormalizer σ, ∀ ht : t ∈ A,
          (actionImage σ).normalizerMonoidHom t ∉
            MulAut.innerSubgroup (actionImage σ) →
          ∃ e : AbsoluteSpace σ ≃ₗ[Closure σ] WordSpace (Closure σ) w,
            ∀ g : J.specialSubgroup,
              absoluteActorRepresentation σ A hl ⟨t, ht⟩ * absoluteRep σ g *
                absoluteActorRepresentation σ A hl ⟨t, ht⟩ =
              wordTransposeInCoordinates e * absoluteRep σ g * wordTransposeInCoordinates e

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
