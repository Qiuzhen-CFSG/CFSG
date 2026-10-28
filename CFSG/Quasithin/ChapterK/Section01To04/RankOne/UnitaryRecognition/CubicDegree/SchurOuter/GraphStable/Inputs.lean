module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.TensorWords
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Models

/-!
# The two remaining outer-word steps

These contracts separate label symmetry from displacement. The first must
derive the absence of natural labels from the literal outer Schur-linear
involution, using the restricted-word catalogue. The second may assume that
absence and must estimate the action of the actual scalar-extended actor on
the word. Neither contract assumes a single factor or the Schur degree.

The factor six in the displacement contract is deliberately weak: combined
with rank A ≤ s+1 it already excludes every repeated adjoint word, including
the endpoint s=2. The final GraphStable module owns this assembly.
Source: Guralnick--Malle, Proposition 4.11 and §3.5.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors Representation.BinaryOffender
open Representation.SU3.CubicDegree.SchurOuter
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- The representation-theoretic consequence of the genuine outer involution.
Its proof must transport the action through the perfect image and its central
quotient; list symmetry by itself is not this assertion. -/
@[expose] def OuterLabelSymmetry (s : ℕ) : Prop :=
  ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
    Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)) →
    ∀ t : linearNormalizer σ, t ^ 2 = 1 → SchurNormalizer.IsSchurLinear σ t →
      (actionImage σ).normalizerMonoidHom t ∉ MulAut.innerSubgroup (actionImage σ) →
      naturalCount w = 0

/-- A sufficient displacement estimate on the actual absolute actor. It may
use an adjoint-only word, but cannot assume the word has only one factor. -/
@[expose] def OuterWordDisplacement (s : ℕ) : Prop :=
  ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
    Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)) →
    naturalCount w = 0 →
    ∀ (A : Subgroup (linearNormalizer σ)), IsElementaryTwo A →
      ∀ hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t,
        ∀ t ∈ A, (actionImage σ).normalizerMonoidHom t ∉
          MulAut.innerSubgroup (actionImage σ) →
          wordDegree w ≤ 6 * Module.finrank (Closure σ)
            (AbsoluteSpace σ ⧸ (absoluteActorRepresentation σ A hl).invariants)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
