module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.SuzukiPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.NaturalAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiRootLine
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Opposition

/-!
# Pinned Suzuki coordinates and opposite source lines

Conjugating the Suzuki marking inside its Borel sends the given source
reflection to the standard Weyl matrix. All original split data, root
placements and (6H) hypotheses are retained. The reflection then reverses
both natural coordinate systems. Applying it to the distinguished first
lines identifies the unreflected linear root in V₂ and Ω₁(U₂^s₁) in
Φ(Uₛ₂)/Z(Uₛ₂) with the fourth coordinate lines, with exactly the same
additive labels. This includes m=0.

The final two action formulas expand the corrected whole Suzuki chart on
both literal quotients in the convention θ=titsEnd. They supply the natural
matrix part of (10.7) and (10.11); identifying the two middle source lines
and synchronizing their field labels still requires the mixed commutator
argument. The eighth-power equation is reused from source opposition and
holds for the supplied lifts in N, not merely their Weyl classes.

Source: Fong--Seitz II (1974), pp.221--224, (10.4), (10.7), (10.11),
and the lift relation (10.43), p.232.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- Conjugate only the Suzuki marking inside its full Borel, retaining the
literal source quotient, split group, field, reflections and (6H) relations. -/
def pinnedInput : ReeSixHData Q split n m :=
  { c with
    suzuki := SuzukiPinning.alignedModel Q split 1 m c.suzuki c.suzukiBorel (c.reflections 1)
    suzukiBorel := SuzukiPinning.alignedModel_borel Q split 1 m c.suzuki c.suzukiBorel
      (c.reflections 1) }

theorem pinnedInput_reflection :
    suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel
        ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩ = suzukiWeyl m :=
  SuzukiPinning.alignedModel_reflection Q split 1 m c.suzuki c.suzukiBorel (c.reflections 1)

theorem sourceSuzukiReflection_square : (c.reflections 1).val ^ 2 = 1 :=
  Subtype.ext (by simpa only [pow_two,Subgroup.coe_mul,OneMemClass.coe_one] using
    SuzukiPinning.reflection_square Q split 1 m c.suzuki c.suzukiBorel (c.reflections 1))

/-- The relation on the supplied lifts holds in N itself. -/
theorem sourceReflection_product_eight :
    ((c.reflections 0).val * (c.reflections 1).val)^8 = 1 :=
  ReeSource.ree_reflection_product_eight Q split c.rotation_eight n c.linear_degree_odd m
    c.linear c.linearSylow c.linearBorel c.suzuki c.suzukiBorel c.reflections c.hcore
      (c.reflections 0).val (c.reflections 1).val
      (c.reflections 0).class_eq (c.reflections 1).class_eq

private theorem natural_weyl (v : Representation.SuzukiNatural.W m) :
    Representation.SuzukiNatural.natural m (suzukiWeyl m) v = ![v 3,v 2,v 1,v 0] := by
  ext i
  fin_cases i <;> simp [Representation.SuzukiNatural.natural_apply,suzukiWeyl,
    SuzukiWeylGL,SuzukiWeylMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_four]

/-- The supplied source reflection reverses all four pinned V₂ coordinates. -/
theorem pinnedV2_reflection (v : (V2Section Q split (pinnedInput Q split c)).numerator) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      ((V2Section Q split (pinnedInput Q split c)).numeratorAction
        ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩ v))) =
      let x := V2Coordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk v))
      ![x 3,x 2,x 1,x 0] := by
  exact (V2Coordinates_source Q split (pinnedInput Q split c)
    ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩ v).trans
      (by rw [pinnedInput_reflection,natural_weyl])

/-- The same literal reflection reverses the second natural module. -/
theorem pinnedPhiCenter_reflection
    (v : (phiCenterSection Q split (pinnedInput Q split c)).numerator) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      ((phiCenterSection Q split (pinnedInput Q split c)).numeratorAction
        ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩ v))) =
      let x := phiCenterCoordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk v))
      ![x 3,x 2,x 1,x 0] := by
  rw [phiCenterCoordinates_source,pinnedInput_reflection,natural_weyl]

include c in
theorem simpleLinear_le_suzukiRemainder : simpleRoot Q split 0 ≤ simpleRemainder Q split 1 := by
  intro a ha
  let z := positiveRootEquiv Q split c (.inl 1) ⟨a,ha⟩
  let v := (V2Section Q split c).numeratorAction
    ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
      (inclusion (reflectedLinear_le_suzukiRemainder Q split c) z)
  have he : (v : X ⧸ Q.D) = a := by
    change ((c.reflections 1).val : X ⧸ Q.D) *
      (((c.reflections 1).val : X ⧸ Q.D)⁻¹ * a * (c.reflections 1).val) *
      ((c.reflections 1).val : X ⧸ Q.D)⁻¹ = a
    group
  rw [←he]
  exact v.property

def V2SimpleLinear : simpleRoot Q split 0 →* (V2Section Q split c).Carrier :=
  (QuotientGroup.mk' (V2Section Q split c).denominator).comp
    (inclusion (simpleLinear_le_suzukiRemainder Q split c))

/-- The fourth coordinate uses the same additive label as the first, on the
literal unreflected linear root. -/
theorem pinnedV2_simpleLinear (a : simpleRoot Q split 0) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (V2SimpleLinear Q split (pinnedInput Q split c) a)) =
        ![0,0,0,reflectedLinearCoordinate Q split (pinnedInput Q split c)
          (positiveRootEquiv Q split (pinnedInput Q split c) (.inl 1) a)] := by
  let d := pinnedInput Q split c
  let z := positiveRootEquiv Q split d (.inl 1) a
  have he : (V2Section Q split d).numeratorAction
      ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
        (inclusion (reflectedLinear_le_suzukiRemainder Q split d) z) =
      inclusion (simpleLinear_le_suzukiRemainder Q split d) a := by
    apply Subtype.ext
    change ((c.reflections 1).val : X ⧸ Q.D) *
      (((c.reflections 1).val : X ⧸ Q.D)⁻¹ * a * (c.reflections 1).val) *
      ((c.reflections 1).val : X ⧸ Q.D)⁻¹ = a
    group
  have h := pinnedV2_reflection Q split c
    (inclusion (reflectedLinear_le_suzukiRemainder Q split d) z)
  rw [he] at h
  change V2Coordinates Q split d (Additive.ofMul (V2SimpleLinear Q split d a)) = _ at h
  change V2Coordinates Q split d (Additive.ofMul (V2SimpleLinear Q split d a)) =
    let x := V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d z))
    ![x 3,x 2,x 1,x 0] at h
  dsimp only at h
  rw [V2Coordinates_reflectedLinear] at h
  exact h

/-- The opposite Omega representatives are obtained by the actual reflection
acting on the first distinguished line, inside the literal Frattini subgroup. -/
def phiOppositeOmega (b : CoefficientField m) : (phiCenterSection Q split c).numerator :=
  (phiCenterSection Q split c).numeratorAction
    ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
      (inclusion (shiftedOmega_le_phi Q split c) (shiftedOmegaPoint Q split c b))

theorem phiOppositeOmega_point (b : CoefficientField m) :
    (phiOppositeOmega Q split c b : X ⧸ Q.D) =
      positivePoint Q split c (RingEquiv.refl _) (.inr 2) (0,b) := by
  change ((c.reflections 1).val : X ⧸ Q.D) *
    ((((c.reflections 0).val : X ⧸ Q.D) * (c.reflections 1).val)⁻¹ *
      (suzukiChart Q split c (0,b) : X ⧸ Q.D) *
      (((c.reflections 0).val : X ⧸ Q.D) * (c.reflections 1).val)) *
    ((c.reflections 1).val : X ⧸ Q.D)⁻¹ =
      ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
        (suzukiChart Q split c (0,b) : X ⧸ Q.D) * (c.reflections 0).val
  group

/-- The fourth coordinate of Φ(V)/Z(V) has exactly the first line's label. -/
theorem pinnedPhiCenter_oppositeOmega (b : CoefficientField m) :
    phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (phiOppositeOmega Q split (pinnedInput Q split c) b))) =
        ![0,0,0,shiftedOmegaFieldLabel Q split (pinnedInput Q split c) b] := by
  have h := pinnedPhiCenter_reflection Q split c
    (inclusion (shiftedOmega_le_phi Q split (pinnedInput Q split c))
      (shiftedOmegaPoint Q split (pinnedInput Q split c) b))
  dsimp only at h
  have he := shiftedOmegaFieldLabel_coordinates Q split (pinnedInput Q split c) b
  change phiCenterCoordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (QuotientGroup.mk (inclusion (shiftedOmega_le_phi Q split (pinnedInput Q split c))
      (shiftedOmegaPoint Q split (pinnedInput Q split c) b)))) = _ at he
  rw [he] at h
  exact h

private theorem suzukiChart_actor (a b : CoefficientField m) :
    suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel
      (inclusion le_sup_left (suzukiChart Q split c (a,b))) =
        (matrixRootPoint m a (b+a*titsEnd m a) : SuzukiMatrixGroup m) := by
  rw [suzukiActorEquiv_simpleRoot]
  change ((suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel)
    ((suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel).symm
      (matrixRootPoint m a (b+a*titsEnd m a))) : SuzukiMatrixGroup m) = _
  rw [MulEquiv.apply_symm_apply]

/-- The complete corrected Suzuki-root action on the literal V₂ quotient.
This is the matrix input to (10.7), before synchronizing the remaining root labels. -/
theorem V2Coordinates_suzukiChart (a b : CoefficientField m)
    (v : simpleRemainder Q split 1) :
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
      ((V2Section Q split c).numeratorAction
        (inclusion le_sup_left (suzukiChart Q split c (a,b))) v))) =
      let x := V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))
      ![x 0+a*x 1+(b+a*titsEnd m a)*x 2+(a^2*titsEnd m a+a*b+titsEnd m b)*x 3,
        x 1+titsEnd m a*x 2+b*x 3,x 2+a*x 3,x 3] := by
  exact (V2Coordinates_source Q split c
    (inclusion le_sup_left (suzukiChart Q split c (a,b))) v).trans
      (by rw [suzukiChart_actor,natural_corrected_root])

/-- The identical corrected root matrix on the second literal Suzuki layer. -/
theorem phiCenterCoordinates_suzukiChart (a b : CoefficientField m)
    (v : (phiCenterSection Q split c).numerator) :
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
      ((phiCenterSection Q split c).numeratorAction
        (inclusion le_sup_left (suzukiChart Q split c (a,b))) v))) =
      let x := phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v))
      ![x 0+a*x 1+(b+a*titsEnd m a)*x 2+(a^2*titsEnd m a+a*b+titsEnd m b)*x 3,
        x 1+titsEnd m a*x 2+b*x 3,x 2+a*x 3,x 3] := by
  exact (phiCenterCoordinates_source Q split c
    (inclusion le_sup_left (suzukiChart Q split c (a,b))) v).trans
      (by rw [suzukiChart_actor,natural_corrected_root])

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
