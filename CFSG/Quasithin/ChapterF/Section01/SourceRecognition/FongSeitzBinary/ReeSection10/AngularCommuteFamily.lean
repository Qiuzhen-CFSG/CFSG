module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAssembly
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RootIntervals

/-!
# A commuting angular family in the synchronized source charts

The adjacent simple-root commutator vanishes in the literal marked quotient.
Right-conjugating it by the first one- and two-step angular words gives the
three disjoint pairs
`(A₀,B₂)`, `(A₁,B₃)`, and `(A₂,B₁)` in the positive Carter order.  The
resulting root-subgroup containments are then applied to the synchronized
charts.  This is a source calculation on the given quotient; no model
identification or additional angular equation is used.

Source: Fong--Seitz II (1974), Section 10, pp.221--224; the adjacent-root
vanishing is the root-interval consequence used in (10.2).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition
open ReeF4.RootPresentationRecognition.AngularPresentation
open Theory.GroupTheory.OrderedRootPresentation
open ReeF4.CentralCovers.TwoPrimary
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

private theorem rightConjugate_commutator (A B : Subgroup (X ⧸ Q.D))
    (z : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ z = ⁅rightConjugate A z,rightConjugate B z⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]

private theorem adjacent_vanishing (c : ReeSixHData Q split n m) :
    ⁅simpleRoot Q split 0, rootAt Q split 1 (Q.simple 0)⁆ = ⊥ := by
  exact adjacent_commutator_eq_bot Q split c.rotation_eight 0 1 (by decide)
    (linearRemainder_le_kernel Q split c) (remainder_le_kernel Q split c)

/-- The first linear and the third Suzuki root commute in the marked quotient. -/
theorem positiveRoot_A0_B2_commute (c : ReeSixHData Q split n m) :
    ⁅positiveRoot Q split (.inl 0), positiveRoot Q split (.inr 2)⁆ = ⊥ := by
  simpa [positiveRoot, positiveKind, positiveWord] using
    (adjacent_vanishing Q split c)

/-- The second linear and the fourth Suzuki root commute in the marked quotient. -/
theorem positiveRoot_A2_B1_commute (c : ReeSixHData Q split n m) :
    ⁅positiveRoot Q split (.inl 2), positiveRoot Q split (.inr 1)⁆ = ⊥ := by
  have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 1 * Q.simple 0) : X ⧸ Q.D))
    (adjacent_vanishing Q split c)
  rw [rightConjugate_commutator] at hh
  rw [show rightConjugate (simpleRoot Q split 0)
      (representative (Q.simple 1 * Q.simple 0) : X ⧸ Q.D) =
      rootAt Q split 0 (Q.simple 1 * Q.simple 0) from rfl] at hh
  rw [rootAt_right Q split 1 (Q.simple 0) (Q.simple 1 * Q.simple 0)
      (representative (Q.simple 1 * Q.simple 0)) (representative_spec _)] at hh
  simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot] at hh
  change ⁅rootAt Q split 0 (Q.simple 1 * Q.simple 0),
    rootAt Q split 1 (Q.simple 0 * (Q.simple 1 * Q.simple 0))⁆ = ⊥ at hh
  simpa [positiveRoot, positiveKind, positiveWord, mul_assoc] using hh

/-- Synchronized chart points in the first commuting pair commute. -/
theorem synchronized_A0_B2_commute (a : CoefficientField m)
    (y z : CoefficientField m) :
    Commute (synchronizedPositivePoint Q split c (.inl 0) a)
      (synchronizedPositivePoint Q split c (.inr 2) (y,z)) := by
  have ha : synchronizedPositivePoint Q split c (.inl 0) a ∈
      positiveRoot Q split (.inl 0) := by
    exact (synchronizedPositiveChart Q split c (.inl 0) a).property
  have hb : synchronizedPositivePoint Q split c (.inr 2) (y,z) ∈
      positiveRoot Q split (.inr 2) := by
    exact (synchronizedPositiveChart Q split c (.inr 2) (y,z)).property
  exact (mem_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (positiveRoot_A0_B2_commute Q split c) ha) _ hb).symm

/-- Synchronized chart points in the second commuting pair commute. -/
theorem synchronized_A2_B1_commute (a : CoefficientField m)
    (y z : CoefficientField m) :
    Commute (synchronizedPositivePoint Q split c (.inl 2) a)
      (synchronizedPositivePoint Q split c (.inr 1) (y,z)) := by
  have ha : synchronizedPositivePoint Q split c (.inl 2) a ∈
      positiveRoot Q split (.inl 2) := by
    exact (synchronizedPositiveChart Q split c (.inl 2) a).property
  have hb : synchronizedPositivePoint Q split c (.inr 1) (y,z) ∈
      positiveRoot Q split (.inr 1) := by
    exact (synchronizedPositiveChart Q split c (.inr 1) (y,z)).property
  exact (mem_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (positiveRoot_A2_B1_commute Q split c) ha) _ hb).symm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
