module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.Torus
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.CentralHigherGeneration.Exchange

/-!
# Exact lower-exchange contracts after arms-torus normalization

The two polynomial identities below use the actual D₄ folded marking.
Their correction words lie strictly above both exchanged roots. The proved
arms-torus normalization keeps all long sections and every supplied upper
relation, so these two remaining calculations suffice for the requested
lower normalization. Their proofs are still explicit inputs here.

Source: GLS3 §2.4.5(b)(4)–(5) and §6.1;
Aschbacher–Smith I.1.3 (PDF p.418).
-/

@[expose] public section
open Triality.Standard PerfectCentralCovering
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.RadicalCoordinates.Centers
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one

namespace LowerNormalization
variable {E : Type*} [Group E] {f : E →* G}

/-- The exact short–short exchange, including both shifted cubic traces. -/
def ShortPairRelation (L : RootSections 1 Nat.zero_lt_one f) : Prop :=
  ∀ s t : ExtensionField P,
    L.shortRoot 0 (.ofAdd s) * L.shortRoot 1 (.ofAdd t) =
      L.shortRoot 1 (.ofAdd t) * L.shortRoot 0 (.ofAdd s) *
        L.shortRoot 2 (.ofAdd (higherCoefficient P s t)) *
        L.longRoot 1 (.ofAdd (cubicTrace P (s * fieldFrobenius P s *
          fieldFrobenius P (fieldFrobenius P t)))) *
        L.longRoot 2 (.ofAdd (cubicTrace P (s * fieldFrobenius P t *
          fieldFrobenius P (fieldFrobenius P t))))

/-- The exact mixed exchange in the same folded marking. -/
def MixedPairRelation (L : RootSections 1 Nat.zero_lt_one f) : Prop :=
  ∀ (s : ExtensionField P) (t : fixedField P),
    L.shortRoot 0 (.ofAdd s) * L.longRoot 0 (.ofAdd t) =
      L.longRoot 0 (.ofAdd t) * L.shortRoot 0 (.ofAdd s) *
        L.shortRoot 1 (.ofAdd (s * t.val)) *
        L.shortRoot 2 (.ofAdd (s * fieldFrobenius P s * t.val)) *
        L.longRoot 1 (.ofAdd (cubicNorm P s * t))

private def shortParameters (i : Fin 3) (t : ExtensionField P) :
    PositiveParameters 1 Nat.zero_lt_one := (Function.update 0 i t, 0)

private def longParameters (i : Fin 3) (t : fixedField P) :
    PositiveParameters 1 Nat.zero_lt_one := (0, Function.update 0 i t)

/-- The short–short formula supplies precisely the `(0,2)` collector exchange. -/
theorem ShortPairRelation.pairExchange {L : RootSections 1 Nat.zero_lt_one f}
    (h : ShortPairRelation L) : PairExchange L 0 2 := by
  intro a b
  refine ⟨[(3, shortParameters 2 (higherCoefficient P (a.1 0) (b.1 1))),
    (4, longParameters 1 (cubicTrace P (a.1 0 * fieldFrobenius P (a.1 0) *
      fieldFrobenius P (fieldFrobenius P (b.1 1))))),
    (5, longParameters 2 (cubicTrace P (a.1 0 * fieldFrobenius P (b.1 1) *
      fieldFrobenius P (fieldFrobenius P (b.1 1)))))], ?_, ?_⟩
  · simp [height]
  · simpa [RootSections.factor, FilteredCollection.wordProduct,
      shortParameters, longParameters, mul_assoc] using h (a.1 0) (b.1 1)

/-- The mixed formula supplies precisely the `(0,1)` collector exchange. -/
theorem MixedPairRelation.pairExchange {L : RootSections 1 Nat.zero_lt_one f}
    (h : MixedPairRelation L) : PairExchange L 0 1 := by
  intro a b
  refine ⟨[(2, shortParameters 1 (a.1 0 * (b.2 0).val)),
    (3, shortParameters 2 (a.1 0 * fieldFrobenius P (a.1 0) * (b.2 0).val)),
    (4, longParameters 1 (cubicNorm P (a.1 0) * b.2 0))], ?_, ?_⟩
  · simp [height]
  · simpa [RootSections.factor, FilteredCollection.wordProduct,
      shortParameters, longParameters, mul_assoc] using h (a.1 0) (b.2 0)

end LowerNormalization

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
