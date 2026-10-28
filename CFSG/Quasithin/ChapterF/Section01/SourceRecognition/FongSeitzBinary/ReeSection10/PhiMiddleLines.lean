module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PinnedNatural

/-!
# All four source lines in the second Suzuki natural section

Relations (10.2)(iii) and (v) identify the two middle lines of
Φ(Uₛ₂)/Z(Uₛ₂). The first relation puts a perpendicular linear-root vector
in the first two coordinate positions. Applying the second relation to its
literal reflection removes the first coordinate. This argument works also
when q = 2, without a nontrivial Cartan assumption. The reflection gives
the third axis with exactly the same additive label as the second.

Unique source products show that the second-axis map is injective; its
order makes it bijective. Together with the already identified Omega axes,
this constructs a four-root product realizing every natural coordinate
vector. The mixed commutator into the first Omega root is computed in the
source group itself. Its coefficient retains both additive labels explicitly;
their synchronization with V₂ and the linear section is still required.

Source: Fong--Seitz II (1974), (10.2)(iii),(v), p.221, and the natural
basis preceding (10.11), p.224. OriginalPhiMiddle transports these results
to the literal original Frattini/center quotient and both endpoint squares.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped Pointwise IsMulCommutative commutatorElement
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

include c in
theorem perpendicularLinear_le_phi : positiveRoot Q split (.inl 3) ≤
    phi (simpleRemainder Q split 1) := by
  intro x hx
  change x ∈ (phi (simpleRemainder Q split 1) : Set _)
  rw [←phiProduct_range Q split c]
  exact ⟨(1,⟨x,hx⟩,1,1,1,PUnit.unit),by
    simp only [phiFactors,rootProduct,OneMemClass.coe_one,mul_one,one_mul]⟩

include c in
theorem nextLinear_le_phi : positiveRoot Q split (.inl 2) ≤
    phi (simpleRemainder Q split 1) := by
  intro x hx
  change x ∈ (phi (simpleRemainder Q split 1) : Set _)
  rw [←phiProduct_range Q split c]
  exact ⟨(1,1,1,⟨x,hx⟩,1,PUnit.unit),by
    simp only [phiFactors,rootProduct,OneMemClass.coe_one,mul_one,one_mul]⟩

private def phiCoordinateHom : (phiCenterSection Q split c).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((phiCenterCoordinates Q split c).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (phiCenterSection Q split c).denominator)

private theorem phi_action_first_displacement_eq (u : simpleRoot Q split 1)
    (v : (phiCenterSection Q split c).numerator)
    (hc : ⁅(u : X ⧸ Q.D),(v : X ⧸ Q.D)⁆ ∈
      omegaOneAmbient (positiveRoot Q split (.inr 3))) :
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
      ((phiCenterSection Q split c).numeratorAction (inclusion le_sup_left u) v))) =
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v)) +
      ![shiftedOmegaCoordinate Q split c ⟨_,hc⟩,0,0,0] := by
  let w : omegaOneAmbient (positiveRoot Q split (.inr 3)) := ⟨_,hc⟩
  let y : (phiCenterSection Q split c).numerator := inclusion (shiftedOmega_le_phi Q split c) w
  have hw : (phiCenterSection Q split c).numeratorAction (inclusion le_sup_left u) v =
      y * v := by
    apply Subtype.ext
    change (u : X ⧸ Q.D) * v * (u : X ⧸ Q.D)⁻¹ =
      ⁅(u : X ⧸ Q.D),(v : X ⧸ Q.D)⁆ * v
    simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
  have hh := congrArg (fun z : (phiCenterSection Q split c).numerator =>
    phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk z))) hw
  apply hh.trans
  have h := congrArg Multiplicative.toAdd ((phiCoordinateHom Q split c).map_mul
    (inclusion (shiftedOmega_le_phi Q split c) w) v)
  change phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
    (y * v))) =
    phiCenterCoordinates Q split c (Additive.ofMul (phiShiftedOmega Q split c w)) +
      phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v)) at h
  rw [phiCenterCoordinates_shiftedOmega] at h
  exact h.trans (add_comm _ _)

private theorem perpendicular_first_displacement (a b : CoefficientField m)
    (v : positiveRoot Q split (.inl 3)) :
    ∃ z : CoefficientField m,
      phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
        ((phiCenterSection Q split c).numeratorAction
          (inclusion le_sup_left (suzukiChart Q split c (a,b)))
          (inclusion (perpendicularLinear_le_phi Q split c) v)))) =
      phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
        (inclusion (perpendicularLinear_le_phi Q split c) v))) + ![z,0,0,0] := by
  refine ⟨_, phi_action_first_displacement_eq Q split c _ _ ?_⟩
  have h := c.relations.ten_two_iii_left 1
  have he : ⁅simpleRoot Q split 1,positiveRoot Q split (.inl 3)⁆ =
      omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
    simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,U,Uat,
      positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,
      Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using h
  exact he ▸ commutator_mem_commutator (suzukiChart Q split c (a,b)).property v.property

private theorem next_omega_first_displacement (b : CoefficientField m)
    (v : positiveRoot Q split (.inl 2)) :
    ∃ z : CoefficientField m,
      phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
        ((phiCenterSection Q split c).numeratorAction
          (inclusion le_sup_left (suzukiChart Q split c (0,b)))
          (inclusion (nextLinear_le_phi Q split c) v)))) =
      phiCenterCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
        (inclusion (nextLinear_le_phi Q split c) v))) + ![z,0,0,0] := by
  refine ⟨_, phi_action_first_displacement_eq Q split c _ _ ?_⟩
  have h := c.relations.ten_two_v 1
  have he : ⁅omegaOneAmbient (simpleRoot Q split 1),positiveRoot Q split (.inl 2)⁆ ≤
      omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
    simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,U,Uat,
      positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,
      Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using h
  apply he
  apply commutator_mem_commutator _ v.property
  rw [suzukiChart_apply]
  simp only [zero_mul,add_zero]
  rw [←suzukiOmegaParameter_range Q split 1 m c.suzuki c.suzukiBorel]
  exact ⟨Multiplicative.ofAdd b,rfl⟩

/-- The actual reflection identifies the two linear middle representatives. -/
theorem phiMiddle_reflection (a : simpleRoot Q split 0) :
    (phiCenterSection Q split c).numeratorAction
      ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
      (inclusion (perpendicularLinear_le_phi Q split c)
        (positiveRootEquiv Q split c (.inl 3) a)) =
      inclusion (nextLinear_le_phi Q split c) (positiveRootEquiv Q split c (.inl 2) a) := by
  apply Subtype.ext
  change ((c.reflections 1).val : X ⧸ Q.D) *
    ((((c.reflections 1).val : X ⧸ Q.D) * (c.reflections 0).val * (c.reflections 1).val)⁻¹ *
      a * (((c.reflections 1).val : X ⧸ Q.D) * (c.reflections 0).val * (c.reflections 1).val)) *
    ((c.reflections 1).val : X ⧸ Q.D)⁻¹ =
      (((c.reflections 1).val : X ⧸ Q.D) * (c.reflections 0).val)⁻¹ * a *
      (((c.reflections 1).val : X ⧸ Q.D) * (c.reflections 0).val)
  group

/-- The second natural line is the literal perpendicular linear root. -/
theorem pinnedPhiCenter_perpendicularLinear (v : positiveRoot Q split (.inl 3)) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      (inclusion (perpendicularLinear_le_phi Q split (pinnedInput Q split c)) v))) =
      let x := phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
        (inclusion (perpendicularLinear_le_phi Q split (pinnedInput Q split c)) v)))
      ![0,x 1,0,0] := by
  let d := pinnedInput Q split c
  let x := phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk
    (inclusion (perpendicularLinear_le_phi Q split d) v)))
  obtain ⟨z,hz⟩ := perpendicular_first_displacement Q split d 1 0 v
  have hz := (phiCenterCoordinates_suzukiChart Q split d 1 0
    (inclusion (perpendicularLinear_le_phi Q split d) v)).symm.trans hz
  change (![x 0+1*x 1+(0+1*titsEnd m 1)*x 2+
      (1^2*titsEnd m 1+1*0+titsEnd m 0)*x 3,
      x 1+titsEnd m 1*x 2+0*x 3,x 2+1*x 3,x 3] : Representation.SuzukiNatural.W m) =
    x + ![z,0,0,0] at hz
  have hx3 : x 3 = 0 := by
    have h := congrFun hz 2
    simpa using h
  have hx2 : x 2 = 0 := by
    have h := congrFun hz 1
    simpa using h
  obtain ⟨a,ha⟩ := (positiveRootEquiv Q split d (.inl 3)).surjective v
  let w := positiveRootEquiv Q split d (.inl 2) a
  have href : phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk
      (inclusion (nextLinear_le_phi Q split d) w))) = ![x 3,x 2,x 1,x 0] := by
    have h := pinnedPhiCenter_reflection Q split c
      (inclusion (perpendicularLinear_le_phi Q split d) (positiveRootEquiv Q split d (.inl 3) a))
    have he := congrArg (fun v : (phiCenterSection Q split d).numerator =>
      phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v)))
      (phiMiddle_reflection Q split d a)
    simpa only [ha] using he.symm.trans h
  obtain ⟨t,ht⟩ := next_omega_first_displacement Q split d 1 w
  have ht := (phiCenterCoordinates_suzukiChart Q split d 0 1
    (inclusion (nextLinear_le_phi Q split d) w)).symm.trans ht
  dsimp only at ht
  rw [href] at ht
  have hx0 : x 0 = 0 := by
    have h := congrFun ht 1
    simpa using h
  change x = ![0,x 1,0,0]
  ext i
  fin_cases i
  · exact hx0
  · rfl
  · exact hx2
  · exact hx3


include c in
/-- The perpendicular root has trivial intersection with the literal center. -/
theorem perpendicularLinear_disjoint_center :
    Disjoint (positiveRoot Q split (.inl 3)) (zeta (simpleRemainder Q split 1)) := by
  apply disjoint_def.mpr
  intro x hx hz
  have hz' : x ∈ omegaOneAmbient (positiveRoot Q split (.inr 1)) := by
    have he : omegaOneAmbient (positiveRoot Q split (.inr 1)) =
        zeta (simpleRemainder Q split 1) := by
      simpa [nConj,positiveRoot,positiveKind,positiveWord,Uat,
        Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using
          c.relations.ten_three_center_remainder 1
    rwa [he]
  let a : positiveRoot Q split (.inl 3) := ⟨x,hx⟩
  let b : omegaOneAmbient (positiveRoot Q split (.inr 1)) := ⟨x,hz'⟩
  have he : rootProduct (phiFactors Q split) (1,a,1,1,1,PUnit.unit) =
      rootProduct (phiFactors Q split) (1,1,b,1,1,PUnit.unit) := by
    simp only [phiFactors,rootProduct,OneMemClass.coe_one,mul_one,one_mul]
    rfl
  exact congrArg (fun p => (p.2.1 : X ⧸ Q.D)) (phiProduct_injective Q split c he)

def phiPerpendicularLinear : positiveRoot Q split (.inl 3) →*
    (phiCenterSection Q split c).Carrier :=
  (QuotientGroup.mk' (phiCenterSection Q split c).denominator).comp
    (inclusion (perpendicularLinear_le_phi Q split c))

theorem phiPerpendicularLinear_injective : Function.Injective (phiPerpendicularLinear Q split c) := by
  apply (phiPerpendicularLinear Q split c).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hz : (x : X ⧸ Q.D) ∈ zeta (simpleRemainder Q split 1) := by
    change inclusion (perpendicularLinear_le_phi Q split c) x ∈
      (QuotientGroup.mk' (phiCenterSection Q split c).denominator).ker at hx
    rw [QuotientGroup.ker_mk'] at hx
    exact hx
  exact Subtype.ext (disjoint_def.mp (perpendicularLinear_disjoint_center Q split c) x.property hz)

/-- Read the second coordinate using the pinned Suzuki marking. -/
def phiPerpendicularCoordinate (v : positiveRoot Q split (.inl 3)) : CoefficientField m :=
  phiCenterCoordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) v)) 1

theorem phiPerpendicularCoordinate_injective : Function.Injective (phiPerpendicularCoordinate Q split c) := by
  intro a b hab
  apply phiPerpendicularLinear_injective Q split (pinnedInput Q split c)
  apply (phiCenterCoordinates Q split (pinnedInput Q split c)).injective
  change phiCenterCoordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) a)) =
      phiCenterCoordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) b))
  have ha := pinnedPhiCenter_perpendicularLinear Q split c a
  have hb := pinnedPhiCenter_perpendicularLinear Q split c b
  apply ha.trans
  apply Eq.trans _ hb.symm
  change (![0,phiPerpendicularCoordinate Q split c a,0,0] : Representation.SuzukiNatural.W m) =
      ![0,phiPerpendicularCoordinate Q split c b,0,0]
  rw [hab]

theorem phiPerpendicularCoordinate_bijective : Function.Bijective (phiPerpendicularCoordinate Q split c) := by
  apply (phiPerpendicularCoordinate_injective Q split c).bijective_of_nat_card_le
  rw [GaloisField.card 2 (2*m+1) (by omega),linear_positiveRoot_card Q split c 3]

def phiPerpendicularLabelHom : positiveRoot Q split (.inl 3) →*
    Multiplicative (CoefficientField m) where
  toFun a := Multiplicative.ofAdd (phiPerpendicularCoordinate Q split c a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) 1)) 1 = 0
    rw [map_one]
    change (phiCenterCoordinates Q split (pinnedInput Q split c)).toLinearEquiv 0 1 = 0
    rw [map_zero]
    rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) (a*b))) 1 =
      phiCenterCoordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) a)) 1 +
      phiCenterCoordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) b)) 1
    rw [map_mul]
    exact congrFun ((phiCenterCoordinates Q split (pinnedInput Q split c)).toLinearEquiv.map_add
      (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) a))
      (Additive.ofMul (phiPerpendicularLinear Q split (pinnedInput Q split c) b))) 1

def phiPerpendicularLabel : positiveRoot Q split (.inl 3) ≃*
    Multiplicative (CoefficientField m) :=
  MulEquiv.ofBijective (phiPerpendicularLabelHom Q split c)
    (Multiplicative.ofAdd.bijective.comp (phiPerpendicularCoordinate_bijective Q split c))

/-- Both middle lines use this same additive field label. Its later
multiplicative synchronization is not assumed. -/
def phiPerpendicularFieldLabel (σ : CoefficientField m ≃+* CoefficientField m) :
    CoefficientField m ≃+ CoefficientField m :=
  ((linearChart Q split (pinnedInput Q split c) σ).trans
    ((positiveRootEquiv Q split (pinnedInput Q split c) (.inl 3)).trans
      (phiPerpendicularLabel Q split c))).toAdditive

theorem pinnedPhiCenter_nextLinear (a : simpleRoot Q split 0) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      (inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
        (positiveRootEquiv Q split (pinnedInput Q split c) (.inl 2) a)))) =
      ![0,0,phiPerpendicularCoordinate Q split c
        (positiveRootEquiv Q split (pinnedInput Q split c) (.inl 3) a),0] := by
  let d := pinnedInput Q split c
  have h := pinnedPhiCenter_reflection Q split c
    (inclusion (perpendicularLinear_le_phi Q split d) (positiveRootEquiv Q split d (.inl 3) a))
  have he := congrArg (fun v : (phiCenterSection Q split d).numerator =>
    phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v)))
    (phiMiddle_reflection Q split d a)
  have h := he.symm.trans h
  dsimp only at h
  rw [pinnedPhiCenter_perpendicularLinear] at h
  exact h

theorem pinnedPhiCenter_perpendicular_fieldLabel
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      (inclusion (perpendicularLinear_le_phi Q split (pinnedInput Q split c))
        (positiveChart Q split (pinnedInput Q split c) σ (.inl 3) a)))) =
      ![0,phiPerpendicularFieldLabel Q split c σ a,0,0] :=
  pinnedPhiCenter_perpendicularLinear Q split c _

theorem pinnedPhiCenter_next_fieldLabel
    (σ : CoefficientField m ≃+* CoefficientField m) (a : CoefficientField m) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      (inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
        (positiveChart Q split (pinnedInput Q split c) σ (.inl 2) a)))) =
      ![0,0,phiPerpendicularFieldLabel Q split c σ a,0] :=
  pinnedPhiCenter_nextLinear Q split c _


/-- An actual commutator coefficient before synchronization of the additive
labels. The equality is in the source group, not just its natural quotient. -/
theorem pinned_perpendicularLinear_commutator
    (σ : CoefficientField m ≃+* CoefficientField m) (a b y : CoefficientField m) :
    ⁅(suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D),
      positivePoint Q split (pinnedInput Q split c) σ (.inl 3) y⁆ =
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3)
        (0,(shiftedOmegaFieldLabel Q split (pinnedInput Q split c)).symm
          (a * phiPerpendicularFieldLabel Q split c σ y)) := by
  let d := pinnedInput Q split c
  let u := suzukiChart Q split d (a,b)
  let v := positiveChart Q split d σ (.inl 3) y
  have hc : ⁅(u : X ⧸ Q.D),(v : X ⧸ Q.D)⁆ ∈
      omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
    have he : ⁅simpleRoot Q split 1,positiveRoot Q split (.inl 3)⁆ =
        omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
      simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,U,Uat,
        positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,
        Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using
          d.relations.ten_two_iii_left 1
    exact he ▸ commutator_mem_commutator u.property v.property
  let z : omegaOneAmbient (positiveRoot Q split (.inr 3)) := ⟨_,hc⟩
  have hz : shiftedOmegaCoordinate Q split d z =
      a * phiPerpendicularFieldLabel Q split c σ y := by
    have he := phi_action_first_displacement_eq Q split d u
      (inclusion (perpendicularLinear_le_phi Q split d) v) hc
    have he := (phiCenterCoordinates_suzukiChart Q split d a b
      (inclusion (perpendicularLinear_le_phi Q split d) v)).symm.trans he
    dsimp only at he
    have hv := pinnedPhiCenter_perpendicular_fieldLabel Q split c σ y
    change phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk
      (inclusion (perpendicularLinear_le_phi Q split d) v))) = _ at hv
    rw [hv] at he
    have he := congrFun he 0
    simpa using he.symm
  have he : z = shiftedOmegaPoint Q split d
      ((shiftedOmegaFieldLabel Q split d).symm
        (a * phiPerpendicularFieldLabel Q split c σ y)) := by
    apply shiftedOmegaCoordinate_injective Q split d
    change shiftedOmegaCoordinate Q split d z = shiftedOmegaFieldLabel Q split d
      ((shiftedOmegaFieldLabel Q split d).symm
        (a * phiPerpendicularFieldLabel Q split c σ y))
    rw [AddEquiv.apply_symm_apply]
    exact hz
  exact congrArg Subtype.val he

/-- Source representatives of all four standard coordinate axes, combined
using the same label for each reflected pair. -/
def phiNaturalPoint (σ : CoefficientField m ≃+* CoefficientField m)
    (p : Representation.SuzukiNatural.W m) :
    (phiCenterSection Q split (pinnedInput Q split c)).Carrier :=
  let d := pinnedInput Q split c
  let ω := shiftedOmegaFieldLabel Q split d
  let τ := phiPerpendicularFieldLabel Q split c σ
  let v₀ : (phiCenterSection Q split d).Carrier :=
    phiShiftedOmega Q split d (shiftedOmegaPoint Q split d (ω.symm (p 0)))
  let v₁ : (phiCenterSection Q split d).Carrier :=
    phiPerpendicularLinear Q split d (positiveChart Q split d σ (.inl 3) (τ.symm (p 1)))
  let v₂ : (phiCenterSection Q split d).Carrier :=
    QuotientGroup.mk (inclusion (nextLinear_le_phi Q split d)
      (positiveChart Q split d σ (.inl 2) (τ.symm (p 2))))
  let v₃ : (phiCenterSection Q split d).Carrier :=
    QuotientGroup.mk (phiOppositeOmega Q split d (ω.symm (p 3)))
  v₀ * v₁ * v₂ * v₃

/-- The complete p.224 natural basis is realized by the four literal source
roots, including the binary field. -/
theorem phiNaturalPoint_coordinates (σ : CoefficientField m ≃+* CoefficientField m)
    (p : Representation.SuzukiNatural.W m) :
    phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (phiNaturalPoint Q split c σ p)) = p := by
  let d := pinnedInput Q split c
  let ω := shiftedOmegaFieldLabel Q split d
  let τ := phiPerpendicularFieldLabel Q split c σ
  have h₀ := shiftedOmegaFieldLabel_coordinates Q split d (ω.symm (p 0))
  have h₁ := pinnedPhiCenter_perpendicular_fieldLabel Q split c σ (τ.symm (p 1))
  have h₂ := pinnedPhiCenter_next_fieldLabel Q split c σ (τ.symm (p 2))
  have h₃ := pinnedPhiCenter_oppositeOmega Q split c (ω.symm (p 3))
  let v₀ : Additive (phiCenterSection Q split d).Carrier :=
    Additive.ofMul (phiShiftedOmega Q split d (shiftedOmegaPoint Q split d (ω.symm (p 0))))
  let v₁ : Additive (phiCenterSection Q split d).Carrier :=
    Additive.ofMul (phiPerpendicularLinear Q split d
      (positiveChart Q split d σ (.inl 3) (τ.symm (p 1))))
  let v₂ : Additive (phiCenterSection Q split d).Carrier :=
    Additive.ofMul (QuotientGroup.mk (inclusion (nextLinear_le_phi Q split d)
      (positiveChart Q split d σ (.inl 2) (τ.symm (p 2)))))
  let v₃ : Additive (phiCenterSection Q split d).Carrier :=
    Additive.ofMul (QuotientGroup.mk (phiOppositeOmega Q split d (ω.symm (p 3))))
  change (phiCenterCoordinates Q split d).toLinearEquiv (v₀+v₁+v₂+v₃) = p
  rw [map_add,map_add,map_add]
  change phiCenterCoordinates Q split d v₀ + phiCenterCoordinates Q split d v₁ +
    phiCenterCoordinates Q split d v₂ + phiCenterCoordinates Q split d v₃ = p
  rw [show phiCenterCoordinates Q split d v₀ = ![p 0,0,0,0] from by
        exact h₀.trans (by simp only [ω,AddEquiv.apply_symm_apply]),
      show phiCenterCoordinates Q split d v₁ = ![0,p 1,0,0] from by
        exact h₁.trans (by simp only [τ,AddEquiv.apply_symm_apply]),
      show phiCenterCoordinates Q split d v₂ = ![0,0,p 2,0] from by
        exact h₂.trans (by simp only [τ,AddEquiv.apply_symm_apply]),
      show phiCenterCoordinates Q split d v₃ = ![0,0,0,p 3] from by
        exact h₃.trans (by simp only [ω,d,AddEquiv.apply_symm_apply])]
  ext i
  fin_cases i <;> simp

theorem phiNaturalPoint_bijective (σ : CoefficientField m ≃+* CoefficientField m) :
    Function.Bijective (phiNaturalPoint Q split c σ) := by
  constructor
  · intro p q hpq
    have h := congrArg (fun v => phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul v)) hpq
    simpa only [phiNaturalPoint_coordinates] using h
  · intro v
    refine ⟨phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul v),?_⟩
    apply (phiCenterCoordinates Q split (pinnedInput Q split c)).injective
    exact phiNaturalPoint_coordinates Q split c σ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The exact source basis shape (1,y,y,1), with a common nonzero scalar in
natural coordinates. Thus the first and last Omega parameters may both be
1, as on p.224, and the two linear parameters are the same nonzero y. -/
theorem phi_source_basis (σ : CoefficientField m ≃+* CoefficientField m) :
    ∃ y s : CoefficientField m, y ≠ 0 ∧ s ≠ 0 ∧
      phiCenterCoordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (phiShiftedOmega Q split (pinnedInput Q split c)
          (shiftedOmegaPoint Q split (pinnedInput Q split c) 1))) = ![s,0,0,0] ∧
      phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
        (inclusion (perpendicularLinear_le_phi Q split (pinnedInput Q split c))
          (positiveChart Q split (pinnedInput Q split c) σ (.inl 3) y)))) = ![0,s,0,0] ∧
      phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
        (inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
          (positiveChart Q split (pinnedInput Q split c) σ (.inl 2) y)))) = ![0,0,s,0] ∧
      phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
        (phiOppositeOmega Q split (pinnedInput Q split c) 1))) = ![0,0,0,s] := by
  let d := pinnedInput Q split c
  let s := shiftedOmegaFieldLabel Q split d 1
  let y := (phiPerpendicularFieldLabel Q split c σ).symm s
  have hs : s ≠ 0 := by
    intro hz
    exact one_ne_zero ((shiftedOmegaFieldLabel Q split d).injective
      (hz.trans (map_zero _).symm))
  have hy : y ≠ 0 := by
    intro hz
    have h := congrArg (phiPerpendicularFieldLabel Q split c σ) hz
    change phiPerpendicularFieldLabel Q split c σ
      ((phiPerpendicularFieldLabel Q split c σ).symm s) = _ at h
    rw [AddEquiv.apply_symm_apply,map_zero] at h
    exact hs h
  refine ⟨y,s,hy,hs,shiftedOmegaFieldLabel_coordinates Q split d 1,?_,?_,
    pinnedPhiCenter_oppositeOmega Q split c 1⟩
  · exact (pinnedPhiCenter_perpendicular_fieldLabel Q split c σ y).trans
      (by dsimp only [y]; rw [AddEquiv.apply_symm_apply])
  · exact (pinnedPhiCenter_next_fieldLabel Q split c σ y).trans
      (by dsimp only [y]; rw [AddEquiv.apply_symm_apply])

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
