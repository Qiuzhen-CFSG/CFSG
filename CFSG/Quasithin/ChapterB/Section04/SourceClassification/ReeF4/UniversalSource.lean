module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4.FiniteExhaustion
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Source

/-!
# Literal Ree FF exclusion with all concrete F4 universality inputs discharged

The incoming-isogeny assembly supplies universality of the actual algebraic
F4 carrier from the full semisimple-center theorem. The original layer,
quotient marking and FF action then use the checked finite irreducibility and
exhaustion consumer. Remaining premises are finite tensor distinction, the
actual odd-order class bound, and universal center containment, each with an
independent source producer. No local FF bound or classifier is assumed.

Source: Aschbacher–Smith B.4.2; GLS3 1.9.5(h), 1.12.5(b); Steinberg (1963), 12.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Actual source exclusion after the concrete universal-version assembly. -/
theorem reeF4_excluded_of_finite_distinction_classes_and_centers
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    {m : ℕ} (hm : 0 < m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (hcenters : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      ∀ (H : Variety F) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
        ∀ T : ClosedSubgroup H, IsMaximalTorus T →
          Subgroup.center (Variety.Point H) ≤ T.toSubgroup)
    (hunique : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2]
      (B C : ZMod (2 * m + 1) → AlgebraicFactor F),
      (∀ i, (B i).IsExceptionalBasic) → (∀ i, (C i).IsExceptionalBasic) →
      Nonempty (Equiv
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ
        (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) C).ρ) →
      ∀ i, AreEquivalentRepresentations (B i).action (C i).action)
    (hclasses : Nat.card (ConjClasses.mk '' {g : _root_.ReeF4.Model m | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (Classification.Steinberg.RestrictedWeight m)) : False := by
  apply reeF4_excluded_of_finite_distinction_and_class_bound h hff hm e _ hunique hclasses
  intro F _ _ _
  exact Classification.Steinberg.Geometry.carrier_isUniversalVersion_of_semisimple_centers
    (hcenters F)

end CFSG.Quasithin.ChapterB.SourceClassification
