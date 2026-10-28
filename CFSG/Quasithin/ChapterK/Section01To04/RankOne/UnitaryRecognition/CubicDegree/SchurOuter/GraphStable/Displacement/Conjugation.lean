module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Displacement.Inputs
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.ScalarRigidity
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation.Adjoint
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation.Tensor
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation.Transport

/-!
# Outer conjugation coordinates from adjoint geometry

For each Frobenius embedding occurring in the given word, construct the
geometric adjoint intertwiner on its actual bundled factor. Tensor these
operators and their coordinates, keeping every trivial factor. The literal
Schur-linear actor has the same target representatives after scalar extension;
its square-one equation gives the required conjugation on the original
absolute module through the supplied representation equivalence.

The final theorem supplies the `AdjointGraphIntertwiner` witnesses from the
finite-field and central-kernel hypotheses. The geometric construction passes
through the perfect action image and its genuine central quotient, retains the
unitary conjugator, and transports an arbitrary Hermitian basis to transpose
coordinates. No adjoint Schur model, Schur degree, displacement estimate, or
single-factor assumption is used; natural-label absence remains the explicit
premise of `OuterTensorConjugation`.
The numerical consumer is `outerWordDisplacement_of_tensor_conjugation` in the
parent's `Displacement` module, which is deliberately not imported here.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32, with §2.2 and §3.5.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Representation Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors Representation.BinaryOffender
open Representation.SU3.CubicDegree.SchurOuter
open Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
open Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
open Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
open Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- Factorwise geometric intertwiners give the exact outer tensor conjugation
contract on the actual absolute module. The independent geometry premise must
still be discharged from the source field and central-kernel hypotheses. -/
theorem outerTensorConjugation_of_adjointGraphIntertwiners (s : ℕ)
    (hgeom : ∀ (ι : F →+* Closure σ) (t : linearNormalizer σ), t ^ 2 = 1 →
      (actionImage σ).normalizerMonoidHom t ∉ MulAut.innerSubgroup (actionImage σ) →
      AdjointGraphIntertwiner J ι (actionHom σ) ((actionImage σ).normalizerMonoidHom t)) :
    OuterTensorConjugation J σ s := by
  intro ι w _ he hn A hA hl t ht ho
  obtain ⟨E⟩ := he
  have ht2 : t ^ 2 = 1 := by
    let : IsElementaryAbelian 2 A := hA.2
    exact elemPow_eq_one_of_isElementaryAbelian t ht
  let R := fun g h : J.specialSubgroup =>
    actionHom σ h = (actionImage σ).normalizerMonoidHom t (actionHom σ g)
  have hf (κ : F →+* Closure σ) :
      ∃ S c : Space (Closure σ) .adjoint ≃ₗ[Closure σ] Space (Closure σ) .adjoint,
        (∀ x, c (S x) = adjointTranspose (c x)) ∧
        ∀ g h, R g h →
          S.toLinearMap * factorRep κ .adjoint (MinimalDegree.specialLinearInclusion J g) =
            factorRep κ .adjoint (MinimalDegree.specialLinearInclusion J h) * S.toLinearMap := by
    exact factor_intertwiner_of_adjointGraphIntertwiner J κ
      (MinimalDegree.specialLinearInclusion J) (fun _ => rfl) (actionHom σ)
      ((actionImage σ).normalizerMonoidHom t) (hgeom κ t ht2 ho)
  obtain ⟨S, c, hc, hS⟩ :=
    word_intertwiner_of_adjoint_intertwiners (MinimalDegree.specialLinearInclusion J) R hf ι w hn
  have ha2 : (⟨t, ht⟩ : A) * ⟨t, ht⟩ = 1 := by
    apply Subtype.ext
    change t * t = 1
    simpa only [pow_two] using ht2
  have hT2 : absoluteActorRepresentation σ A hl ⟨t, ht⟩ *
      absoluteActorRepresentation σ A hl ⟨t, ht⟩ = 1 := by
    rw [← map_mul, ha2, map_one]
  refine conjugation_eq_of_word_intertwiner (absoluteRep σ) w (MinimalDegree.word J ι w)
    E (absoluteActorRepresentation σ A hl ⟨t, ht⟩) hT2 S c hc ?_
  intro g
  exact (σ.asGroupHom.rangeRestrict_surjective
    ((actionImage σ).normalizerMonoidHom t (actionHom σ g))).imp (fun h hh =>
      ⟨absoluteActor_intertwines σ A hl ⟨t, ht⟩ hh, hS g h hh⟩)

/-- Every literal outer elementary-two actor on an adjoint-only SU₃ word
induces the same conjugation as tensorwise transpose in suitable coordinates
on the actual absolute representation. All geometric premises are discharged
from the source field and central-kernel assumptions, including when `s = 2`. -/
theorem outerTensorConjugation [Finite F] {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hk : σ.ker ≤ Subgroup.center J.specialSubgroup) :
    OuterTensorConjugation J σ s :=
  outerTensorConjugation_of_adjointGraphIntertwiners J σ s
    (adjointGraphIntertwiner_of_outer_involution J hs hcard hconj σ hk)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
