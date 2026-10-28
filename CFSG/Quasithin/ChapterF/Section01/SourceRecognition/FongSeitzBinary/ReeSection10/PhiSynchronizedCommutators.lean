module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiSynchronization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiCommutators

/-!
# Mixed commutators with the synchronized Φ chart

The perpendicular linear Φ-line is now read using the same multiplicative
linear chart as the first natural section.  The source (10.2)(iii)
commutator calculation therefore produces the synchronized coefficient
`a * synchronizedPhiLabel y` in the shifted Omega root.  This is the literal
second-natural analogue of (10.8), and is independent of the later torus and
signed Weyl tables. The equality between the common middle-line label
and the Omega label remains a later comparison.

Source: Fong--Seitz II (1974), (10.11), printed p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

theorem synchronized_perpendicularLinear_commutator
    (a b y : CoefficientField m) :
    ⁅(suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D),
      synchronizedPositivePoint Q split c (.inl 3) y⁆ =
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3)
        (0,(shiftedOmegaFieldLabel Q split (pinnedInput Q split c)).symm
          (a * synchronizedPhiLabel Q split c y)) := by
  let d := pinnedInput Q split c
  let v := synchronizedPositiveChart Q split c (.inl 3) y
  let e := positiveChart Q split d (RingEquiv.refl _) (.inl 3)
  let z := e.symm v
  have hv : e z = v := e.apply_symm_apply v
  have hl : phiPerpendicularFieldLabel Q split c (RingEquiv.refl _) z =
      synchronizedPhiLabel Q split c y := by
    change phiPerpendicularCoordinate Q split c (e z) =
      phiPerpendicularCoordinate Q split c v
    rw [hv]
  have h := pinned_perpendicularLinear_commutator Q split c (RingEquiv.refl _) a b z
  change ⁅(suzukiChart Q split d (a,b) : X ⧸ Q.D), (e z : X ⧸ Q.D)⁆ = _ at h
  rw [hv,hl] at h
  exact h


/-- The same coefficient in the source right-commutator convention. -/
theorem synchronized_perpendicularLinear_right_commutator
    (a b y : CoefficientField m) :
    (synchronizedPositivePoint Q split c (.inl 3) y)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 3) y *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) =
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3)
        (0,(shiftedOmegaFieldLabel Q split (pinnedInput Q split c)).symm
          (a * synchronizedPhiLabel Q split c y)) := by
  let d := pinnedInput Q split c
  let v := synchronizedPositiveChart Q split c (.inl 3) y
  let e := positiveChart Q split d (RingEquiv.refl _) (.inl 3)
  let z := e.symm v
  have hv : e z = v := e.apply_symm_apply v
  have hl : phiPerpendicularFieldLabel Q split c (RingEquiv.refl _) z =
      synchronizedPhiLabel Q split c y := by
    change phiPerpendicularCoordinate Q split c (e z) =
      phiPerpendicularCoordinate Q split c v
    rw [hv]
  have h := pinned_perpendicularLinear_right_commutator Q split c (RingEquiv.refl _) a b z
  change (e z : X ⧸ Q.D)⁻¹ * (suzukiChart Q split d (a,b) : X ⧸ Q.D)⁻¹ *
    (e z : X ⧸ Q.D) * suzukiChart Q split d (a,b) = _ at h
  rw [hv,hl] at h
  exact h


/-- The next linear line gives the two leading coordinates of (10.11)(ii). -/
theorem synchronizedPhiNext_commutator_coordinates (a b y : CoefficientField m) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      (phiRightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
          (synchronizedPositiveChart Q split c (.inl 2) y))))) =
      ![b * synchronizedPhiLabel Q split c y,
        titsEnd m a * synchronizedPhiLabel Q split c y,0,0] := by
  have h := phiRightCommutator_coordinates Q split (pinnedInput Q split c) a b
    (inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
      (synchronizedPositiveChart Q split c (.inl 2) y))
  dsimp only at h
  rw [synchronizedPhiNextCoordinates] at h
  simpa only [Matrix.cons_val, Fin.isValue, Matrix.head_cons, mul_zero,
    zero_add, add_zero] using h

/-- The opposite Omega line gives (10.11)(iii), with its actual additive label. -/
theorem synchronizedPhiOpposite_commutator_coordinates (a b y : CoefficientField m) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      (phiRightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (phiOppositeOmega Q split (pinnedInput Q split c) y)))) =
      ![(a^2*titsEnd m a+a*b+titsEnd m b) *
          shiftedOmegaFieldLabel Q split (pinnedInput Q split c) y,
        (b+a*titsEnd m a) * shiftedOmegaFieldLabel Q split (pinnedInput Q split c) y,
        a * shiftedOmegaFieldLabel Q split (pinnedInput Q split c) y,0] := by
  have h := phiRightCommutator_coordinates Q split (pinnedInput Q split c) a b
    (phiOppositeOmega Q split (pinnedInput Q split c) y)
  dsimp only at h
  rw [pinnedPhiCenter_oppositeOmega] at h
  simpa only [Matrix.cons_val, Fin.isValue, Matrix.head_cons, mul_zero,
    zero_add, add_zero] using h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
