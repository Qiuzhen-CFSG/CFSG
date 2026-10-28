module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiCentralCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.RootLine

/-!
# Support of the printed mixed linear coefficient

The right commutator of the reflected linear root and the simple linear root is
in the literal Frattini subgroup of the Suzuki remainder.  The source
five-factor product consequently gives its unique endpoint and middle-root
support.  This is the source-level support used to determine the coefficient
`f` on printed pp.226--227; no quotient or Weyl-class replacement occurs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
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

/-- The printed mixed right commutator has literal five-factor support. -/
theorem synchronized_mixedPhi_decomposition (a b : CoefficientField m) :
    ∃ p : omegaOneAmbient (positiveRoot Q split (.inr 3)),
      ∃ q : positiveRoot Q split (.inl 3),
      ∃ r : omegaOneAmbient (positiveRoot Q split (.inr 1)),
      ∃ s : positiveRoot Q split (.inl 2),
      ∃ t : omegaOneAmbient (positiveRoot Q split (.inr 2)),
      ((p : X ⧸ Q.D) * q * r * s * t : X ⧸ Q.D) =
        (synchronizedPositivePoint Q split c (.inl 1) b)⁻¹ *
          (synchronizedPositivePoint Q split c (.inl 0) a)⁻¹ *
          synchronizedPositivePoint Q split c (.inl 1) b *
          synchronizedPositivePoint Q split c (.inl 0) a := by
  let d := pinnedInput Q split c
  let u : positiveRoot Q split (.inl 0) :=
    synchronizedPositiveChart Q split c (.inl 0) a
  let v : positiveRoot Q split (.inl 1) :=
    synchronizedPositiveChart Q split c (.inl 1) b
  have hu : (u : X ⧸ Q.D) ∈ simpleRemainder Q split 1 :=
    (positiveRoot_le_remainder Q split d (.inl 0) 1 (by decide)) u.property
  have hv : (v : X ⧸ Q.D) ∈ simpleRemainder Q split 1 :=
    (reflectedLinear_le_suzukiRemainder Q split c) v.property
  let k : X ⧸ Q.D := (v : X ⧸ Q.D)⁻¹ * (u : X ⧸ Q.D)⁻¹ * v * u
  have hphi : ⁅simpleRemainder Q split 1, simpleRemainder Q split 1⁆ =
      phi (simpleRemainder Q split 1) := by
    simpa only [nConj, OneMemClass.coe_one, rightConjugate_one] using
      (c.relations.ten_three_frattini 1)
  have hkcomm : ⁅(v : X ⧸ Q.D)⁻¹, (u : X ⧸ Q.D)⁻¹⁆ ∈
      phi (simpleRemainder Q split 1) :=
    hphi ▸ commutator_mem_commutator (inv_mem hv) (inv_mem hu)
  have hk : k ∈ phi (simpleRemainder Q split 1) := by
    change (v : X ⧸ Q.D)⁻¹ * (u : X ⧸ Q.D)⁻¹ * v * u ∈ _
    simpa only [commutatorElement_def, inv_inv] using hkcomm
  have hkset : k ∈ (phi (simpleRemainder Q split 1) : Set (X ⧸ Q.D)) := hk
  rw [← phiProduct_range Q split c] at hkset
  obtain ⟨z, hz⟩ := hkset
  rcases z with ⟨p,q,r,s,t,z⟩
  refine ⟨p,q,r,s,t,?_⟩
  change ((p : X ⧸ Q.D) * q * r * s * t : X ⧸ Q.D) = _
  change ((p : X ⧸ Q.D) * q * r * s * t : X ⧸ Q.D) = k
  simpa only [phiFactors, rootProduct, OneMemClass.coe_one, one_mul, mul_one, mul_assoc] using hz
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
