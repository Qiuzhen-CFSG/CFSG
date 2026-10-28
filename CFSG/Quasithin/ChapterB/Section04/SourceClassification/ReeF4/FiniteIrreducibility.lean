module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Irreducibility

/-!
# The original B.4.2 Ree action with finite irreducibility discharged

The actual finite root-curve and invariant-pairing proof supplies irreducibility
of every exceptional tensor used by the source fixed-space estimate. This
consumer keeps the original layer, quotient marking and FF offender. Actual
algebraic universality, finite parameter distinction and exhaustion remain
explicit with their independent source producers.

Source: Aschbacher–Smith B.4.2; Steinberg (1963), 12.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Actual source exclusion with the finite irreducibility premise proved. -/
theorem reeF4_excluded_of_finite_distinction_and_exhaustion
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    {m : ℕ} (hm : 0 < m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (hU : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hunique : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      (B C : ZMod (2 * m + 1) → AlgebraicFactor F),
      (∀ i, (B i).IsExceptionalBasic) → (∀ i, (C i).IsExceptionalBasic) →
      Nonempty (Equiv
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) C).ρ) →
      ∀ i, AreEquivalentRepresentations (B i).action (C i).action)
    (hreal : ∀ (F W : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (σ : Representation F (_root_.ReeF4.Model m) W), Representation.IsIrreducible σ →
      ∃ B : ZMod (2 * m + 1) → AlgebraicFactor F,
        (∀ i, (B i).IsExceptionalBasic) ∧ Nonempty (Equiv σ
          (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ)) : False := by
  apply reeF4_excluded_of_finite_tensor_classification h hff hm e _ hunique hreal
  intro F _ _ _ B hB
  exact Classification.Steinberg.FiniteRootAction.exceptionalTensor_irreducible
    m B (hU F) hB (Classification.coefficientHom F m)

end CFSG.Quasithin.ChapterB.SourceClassification
