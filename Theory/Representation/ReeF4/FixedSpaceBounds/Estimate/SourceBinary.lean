module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.TensorSource
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.SchurCodimension
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.SourceCover
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight

/-!
# Binary Ree involution bounds from the genuine finite tensor theorem

The three finite Steinberg clauses are irreducibility of every restricted
basic tensor, distinction of its actual algebraic factors, and realization of
every irreducible representation as that tensor. Given these full clauses,
coefficient Frobenius supplies the exact factor period. The proved basic
involution ranks and Schur-field codimension identity then give the binary
bound on the original module.

All local torus, basic-rank, raw algebraic highest-weight, coefficient-Frobenius,
and descent premises are discharged. This remains an honest conditional
assembly until finite restriction, distinction and realization are proved;
no such classification is asserted by this file.
Source: GLS3 2.8.2, 2.8.5 and 2.8.6; Guralnick–Malle II, Lemma 8.8.
-/

public section
open Theory.AlgebraicGroup Representation
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate
universe v

/-- The full binary source estimate, conditional only on the three genuine
finite exceptional tensor classification clauses. The basic ranks, character
Frobenius, nontrivial factor, and actual Schur-field descent are proved. -/
theorem binaryModelInvolutionBound_of_finite_tensor_classification {m : ℕ} (hm : 1 ≤ m)
    (hirr : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      (B : ZMod (2 * m + 1) → AlgebraicFactor F),
      (∀ i, (B i).IsExceptionalBasic) → IsIrreducible
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ)
    (hunique : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      (B C : ZMod (2 * m + 1) → AlgebraicFactor F),
      (∀ i, (B i).IsExceptionalBasic) → (∀ i, (C i).IsExceptionalBasic) →
      Nonempty (Equiv
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) C).ρ) →
      ∀ i, AreEquivalentRepresentations (B i).action (C i).action)
    (hreal : ∀ (F W : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (σ : Representation F (Model m) W), IsIrreducible σ →
      ∃ B : ZMod (2 * m + 1) → AlgebraicFactor F,
        (∀ i, (B i).IsExceptionalBasic) ∧ Nonempty (Equiv σ
          (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ)) :
    BinaryModelInvolutionBound.{v} m := by
  intro V _ _ _ ρ hi hf t ht ht2
  let : ρ.IsIrreducible := hi
  let F := Representation.FrobeniusTensor.Closure ρ
  let σ := Representation.FrobeniusTensor.absoluteRep ρ
  have hσ : Function.Injective σ := Representation.FrobeniusTensor.absoluteRep_injective ρ hf
  obtain ⟨B, hB, ⟨e⟩⟩ := hreal F _ σ inferInstance
  obtain ⟨_, hperiod, hshift⟩ := Classification.factorization_consequences σ hσ
    (Classification.splitEmbedding (Classification.coefficientHom F m))
    (hirr F) (hunique F) B hB e
    (Classification.Steinberg.SourceHighestWeight.character_shift
      (Classification.coefficientHom F m) B hB)
  apply binary_fixedCodim_ge_of_period_estimate ρ (Subgroup.zpowers t) hperiod
  intro s hs hsn hc
  exact exceptionalTensor_bound_of_faithful hm σ hσ B hB e hs hsn
    (hshift s hc) t ht ht2

end ReeF4.FixedSpaceEstimate
