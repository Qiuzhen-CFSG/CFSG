module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.ReeF4.ElementaryTwoBound
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.FiniteSource

/-!
# The original Ree component action with intrinsic model bounds discharged

The actual elementary-subgroup estimate and the assembled finite tensor bound
supply the two model inputs of the component-recognition F-module argument.
Its original generalized Fitting subgroup, quotient marking and representation
are retained. The remaining earlier-source premises are the universal
semisimple-center theorem and the literal odd-order class bound.

Source: Aschbacher–Smith B.1; Guralnick–Malle II, Lemma 8.8.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Theory.AlgebraicGroup
universe u v
variable {H : Type u} [Group H] [Finite H] (N : Subgroup H)
  [N.Normal] [IsQuasisimple N]

/-- The original component-recognition FF action is excluded without an
additional intrinsic rank or involution-bound premise. -/
theorem not_ff_of_class_bound_and_semisimple_centers {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* _root_.ReeF4.Model m)
    (hcenters : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      ∀ (K : Variety F) [AlgebraicGroup K], IsSemisimpleAlgebraicGroup K →
        ∀ T : ClosedSubgroup K, IsMaximalTorus T →
          Subgroup.center (Variety.Point K) ≤ T.toSubgroup)
    (hclasses : Nat.card (ConjClasses.mk '' {g : _root_.ReeF4.Model m | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (_root_.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.RestrictedWeight m))
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    [IsIrreducible (ρ.comp N.subtype)] (hf : Function.Injective ρ) : ¬ IsFFModule ρ := by
  have hb := _root_.ReeF4.FixedSpaceEstimate.coverInvolutionBound_of_class_bound_and_semisimple_centers
    hcenters hclasses hm
  exact not_ff_of_absoluteGap N ρ hf (absoluteGap_of_involution_bound N hm hF e
    (_root_.ReeF4.ElementaryTwoBound.card_le m hm) hb)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
