module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4.FiniteIrreducibility
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Exhaustion

/-!
# The original Ree FF exclusion reduced to distinction and odd-order classes

The finite irreducibility theorem and the exact modular family count now
construct the required exceptional tensor realization. The original B.4.2
layer, quotient marking and FF action feed the same fixed-space contradiction.
The only remaining inputs are actual algebraic universality, finite parameter
distinction and the genuine q² bound for the original carrier's odd-order
conjugacy classes. Their independent producers retain final discharge.

Source: Aschbacher–Smith B.4.2; Steinberg (1963), 3.9 and 12.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Actual source exclusion with both finite irreducibility and tensor
realization supplied by the constructed family. -/
theorem reeF4_excluded_of_finite_distinction_and_class_bound
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
    (hclasses : Nat.card (ConjClasses.mk '' {g : _root_.ReeF4.Model m | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (Classification.Steinberg.RestrictedWeight m)) : False := by
  apply reeF4_excluded_of_finite_distinction_and_exhaustion h hff hm e hU hunique
  intro F W _ _ _ _ _ _ σ hσ
  let := hσ
  exact Classification.Steinberg.FiniteRootAction.exists_tensor_of_class_bound
    m (hU F) (Classification.coefficientHom F m) (hunique F) hclasses σ

end CFSG.Quasithin.ChapterB.SourceClassification
