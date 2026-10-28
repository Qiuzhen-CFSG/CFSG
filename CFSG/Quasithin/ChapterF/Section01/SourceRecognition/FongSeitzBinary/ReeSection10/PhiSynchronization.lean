module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SynchronizedCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiCommutators

/-!
# Synchronized coordinates on the second natural section

The mixed V₁/V₂ commutator fixes the multiplicative relabelling of the
linear root.  Transporting that same chart through the two literal
middle Φ-lines gives a single additive label for their coordinates.  The
proof uses the supplied reflection, so the two labels are synchronized in
the source quotient itself, including the binary field.

Source: Fong--Seitz II (1974), (10.6)--(10.11), pp.223--224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The common additive Φ-coordinate label induced by the synchronized
linear chart and the perpendicular middle line. -/
def synchronizedPhiLabel : CoefficientField m ≃+ CoefficientField m :=
  ((synchronizedLinearChart Q split c).trans
    ((positiveRootEquiv Q split (pinnedInput Q split c) (.inl 3)).trans
      (phiPerpendicularLabel Q split c))).toAdditive

theorem synchronizedPhiCoordinates (a : CoefficientField m) :
    phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (inclusion
        (perpendicularLinear_le_phi Q split (pinnedInput Q split c))
        (synchronizedPositiveChart Q split c (.inl 3) a)))) =
      ![0,synchronizedPhiLabel Q split c a,0,0] := by
  let d := pinnedInput Q split c
  let v : positiveRoot Q split (.inl 3) := synchronizedPositiveChart Q split c (.inl 3) a
  have h := pinnedPhiCenter_perpendicularLinear Q split c v
  change phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk
      (inclusion (perpendicularLinear_le_phi Q split d) v))) = _
  rw [h]
  rfl

theorem synchronizedPhiNextCoordinates (a : CoefficientField m) :
    phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (inclusion
        (nextLinear_le_phi Q split (pinnedInput Q split c))
        (synchronizedPositiveChart Q split c (.inl 2) a)))) =
      ![0,0,synchronizedPhiLabel Q split c a,0] := by
  let d := pinnedInput Q split c
  let v : simpleRoot Q split 0 := synchronizedLinearChart Q split c (.ofAdd a)
  have h := pinnedPhiCenter_nextLinear Q split c v
  dsimp only [d, v, synchronizedPositiveChart] at h ⊢
  exact h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
