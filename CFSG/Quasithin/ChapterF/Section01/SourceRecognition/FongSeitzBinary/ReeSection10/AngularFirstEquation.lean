module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAssembly
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RootIntervals

/-!
# The first ordered angular tail equation

The adjacent root interval gives the literal `A₁/B₃` commutation after
right-conjugation by the first Suzuki Weyl word.  The synchronized (10.8)
identity then converts the inverse Suzuki actor into the ordered conjugate
of `B₀` by `B₃`; commuting the resulting `A₁` past `B₃` gives the first
ordered tail equation for `B₀`.  The other ordered angular equations remain
explicit premises of the Section 10 construction.

Source: Fong--Seitz II (1974), Section 10, pp.223--225, (10.8) and the
first ordered tail after the Carter positive-root order.
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

private theorem rc_comm (A B : Subgroup (X ⧸ Q.D)) (z : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ z = ⁅rightConjugate A z,rightConjugate B z⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]

theorem positiveRoot_A1_B3_commute (c : ReeSixHData Q split n m) :
    ⁅positiveRoot Q split (.inl 1), positiveRoot Q split (.inr 3)⁆ = ⊥ := by
  have hbase : ⁅simpleRoot Q split 0, rootAt Q split 1 (Q.simple 0)⁆ = ⊥ := by
    exact adjacent_commutator_eq_bot Q split c.rotation_eight 0 1 (by decide)
      (linearRemainder_le_kernel Q split c) (remainder_le_kernel Q split c)
  have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 1) : X ⧸ Q.D)) hbase
  rw [rc_comm] at hh
  rw [show rightConjugate (simpleRoot Q split 0)
      (representative (Q.simple 1) : X ⧸ Q.D) = rootAt Q split 0 (Q.simple 1) from rfl] at hh
  rw [rootAt_right Q split 1 (Q.simple 0) (Q.simple 1)
      (representative (Q.simple 1)) (representative_spec _)] at hh
  simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot] at hh
  change ⁅rootAt Q split 0 (Q.simple 1),
    rootAt Q split 1 (Q.simple 0 * Q.simple 1)⁆ = ⊥
  exact hh

theorem synchronized_A1_B3_commute (a : CoefficientField m) (y z : CoefficientField m) :
    Commute (synchronizedPositivePoint Q split c (.inl 1) a)
      (synchronizedPositivePoint Q split c (.inr 3) (y,z)) := by
  have ha : synchronizedPositivePoint Q split c (.inl 1) a ∈ positiveRoot Q split (.inl 1) := by
    exact (synchronizedPositiveChart Q split c (.inl 1) a).property
  have hb : synchronizedPositivePoint Q split c (.inr 3) (y,z) ∈ positiveRoot Q split (.inr 3) := by
    exact (synchronizedPositiveChart Q split c (.inr 3) (y,z)).property
  exact (mem_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (positiveRoot_A1_B3_commute Q split c) ha) _ hb).symm

theorem synchronized_A1_B3_conjugate (a b y z : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr 0) (a,b) *
      synchronizedPositivePoint Q split c (.inr 3) (y,z) *
      (synchronizedPositivePoint Q split c (.inr 0) (a,b))⁻¹ =
    synchronizedPositivePoint Q split c (.inl 1) (a*y) *
      synchronizedPositivePoint Q split c (.inr 3) (y,z) := by
  have h8 := synchronized_ten_eight Q split c a (b + a*titsEnd m a) y z
  rw [← suzukiChart_inverse Q split (pinnedInput Q split c) a b] at h8
  have hB0 :
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) =
        synchronizedPositivePoint Q split c (.inr 0) (a,b) := by
    dsimp [synchronizedPositivePoint, synchronizedPositiveChart, positiveChart]
    simp [positiveKind, positiveRootEquiv, positiveLift, positiveWord,
      ReeSource.RootAction.conjugateEquiv]
    rfl
  change (synchronizedPositivePoint Q split c (.inr 3) (y,z))⁻¹ *
      ((suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 3) (y,z) *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ =
      synchronizedPositivePoint Q split c (.inl 1) (a*y) at h8
  rw [hB0] at h8
  simp only [inv_inv] at h8
  change (synchronizedPositivePoint Q split c (.inr 3) (y,z))⁻¹ *
      synchronizedPositivePoint Q split c (.inr 0) (a,b) *
      synchronizedPositivePoint Q split c (.inr 3) (y,z) *
      (synchronizedPositivePoint Q split c (.inr 0) (a,b))⁻¹ =
      synchronizedPositivePoint Q split c (.inl 1) (a*y) at h8
  have hconj := congrArg (fun t => synchronizedPositivePoint Q split c (.inr 3) (y,z) * t) h8
  calc
    synchronizedPositivePoint Q split c (.inr 0) (a,b) *
        synchronizedPositivePoint Q split c (.inr 3) (y,z) *
        (synchronizedPositivePoint Q split c (.inr 0) (a,b))⁻¹ =
      synchronizedPositivePoint Q split c (.inr 3) (y,z) *
        ((synchronizedPositivePoint Q split c (.inr 3) (y,z))⁻¹ *
          synchronizedPositivePoint Q split c (.inr 0) (a,b) *
          synchronizedPositivePoint Q split c (.inr 3) (y,z) *
          (synchronizedPositivePoint Q split c (.inr 0) (a,b))⁻¹) := by group
    _ = synchronizedPositivePoint Q split c (.inr 3) (y,z) *
        synchronizedPositivePoint Q split c (.inl 1) (a*y) := hconj
    _ = synchronizedPositivePoint Q split c (.inl 1) (a*y) *
        synchronizedPositivePoint Q split c (.inr 3) (y,z) :=
      (synchronized_A1_B3_commute Q split c (a*y) y z).eq.symm

theorem synchronized_B0_B3_ordered_tail (a b y z : CoefficientField m) :
    synchronizedSourceRoot Q split c (.inr 0) (PositiveTables.rootChartEquiv m (.inr 0) (a,b)) *
      synchronizedSourceRoot Q split c (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (y,z)) *
      (synchronizedSourceRoot Q split c (.inr 0) (PositiveTables.rootChartEquiv m (.inr 0) (a,b)))⁻¹ =
    OrderedRootPresentation.word (AngularPresentation.Parameter m)
      (fun i => synchronizedSourceRoot Q split c i)
      (tail sourceOrder (.inr 0))
      ((PositiveTables.rootChartEquiv m (.inl 1) (a*y),
        (PositiveTables.rootChartEquiv m (.inr 3) (y,z),
          (PositiveTables.rootChartEquiv m (.inl 3) 0,
            (PositiveTables.rootChartEquiv m (.inr 1) (0,0),
              (PositiveTables.rootChartEquiv m (.inl 2) 0,
                (PositiveTables.rootChartEquiv m (.inr 2) (0,0),
                  (PositiveTables.rootChartEquiv m (.inl 0) 0, PUnit.unit)))))))) := by
  change _ =
    synchronizedSourceRoot Q split c (.inl 1) (PositiveTables.rootChartEquiv m (.inl 1) (a*y)) *
    (synchronizedSourceRoot Q split c (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3) (y,z)) *
    (synchronizedSourceRoot Q split c (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) 0) *
    (synchronizedSourceRoot Q split c (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1) (0,0)) *
    (synchronizedSourceRoot Q split c (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) 0) *
    (synchronizedSourceRoot Q split c (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (0,0)) *
    (synchronizedSourceRoot Q split c (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) 0) * 1))))))
  rw [synchronizedSourceRoot_field Q split c (.inr 0) (a,b),
    synchronizedSourceRoot_field Q split c (.inr 3) (y,z),
    synchronizedSourceRoot_field Q split c (.inl 1) (a*y),
    synchronizedSourceRoot_field Q split c (.inl 3) 0,
    synchronizedSourceRoot_field Q split c (.inr 1) (0,0),
    synchronizedSourceRoot_field Q split c (.inl 2) 0,
    synchronizedSourceRoot_field Q split c (.inr 2) (0,0),
    synchronizedSourceRoot_field Q split c (.inl 0) 0]
  simp only [synchronizedPositivePoint_pair_zero, synchronizedPositivePoint_quartet_zero,
    mul_one]
  exact synchronized_A1_B3_conjugate Q split c a b y z
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
