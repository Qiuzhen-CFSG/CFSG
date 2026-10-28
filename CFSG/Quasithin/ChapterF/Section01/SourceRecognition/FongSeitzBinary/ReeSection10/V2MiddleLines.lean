module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.V2Support
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiCommutators

/-!
# The middle Suzuki lines and the source natural basis of V₂

The first relation in (10.2)(ii) puts U₂^(s₁s₂) in the first coordinate
plane. Reflecting this root and using the five-root commutator support
bounds its displacement by that plane. The third matrix coordinate then
excludes a tilted second line, including q = 2. Reflection identifies
U₂^s₁ with the third axis and preserves its additive label.

The literal Omega subgroup is killed by T₂. The eight-root product and
surjectivity of the natural coordinates show that reading the remaining
Suzuki parameter is an additive equivalence of the coefficient field.
This constructs all four source axes, their product coordinates, and the
basis (1,x,x,1) of (10.4). No multiplicativity of these additive labels or
synchronization with the linear section is asserted.

Source: Fong--Seitz II (1974), (10.2)(ii), pp.221--222, the binary line
characterization on p.222, and (10.4). OriginalV2Middle transports the
same representatives to the original quotient; V2Commutators applies the
basis to the literal source commutator before the comparison in (10.7).
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
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

private def V2CoordinateHom : (V2Section Q split c).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((V2Coordinates Q split c).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (V2Section Q split c).denominator)

private theorem V2Coordinates_T2 (v : (V2Section Q split c).numerator)
    (hv : (v : X ⧸ Q.D) ∈ T2 Q split) :
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v)) = 0 := by
  have hv' : (QuotientGroup.mk v : (V2Section Q split c).Carrier) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hv
  rw [hv']
  exact map_zero (V2Coordinates Q split c).toLinearEquiv

/-- The whole shifted Suzuki root in the literal first natural section. -/
def V2ShiftedSuzuki : positiveRoot Q split (.inr 3) →* (V2Section Q split c).Carrier :=
  (QuotientGroup.mk' (V2Section Q split c).denominator).comp
    (inclusion (positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide)))

/-- Its reflected root, with the same source lift conventions. -/
def V2OppositeSuzuki : positiveRoot Q split (.inr 2) →* (V2Section Q split c).Carrier :=
  (QuotientGroup.mk' (V2Section Q split c).denominator).comp
    (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 1 (by decide)))

private theorem V2_shifted_first_displacement (a b : CoefficientField m)
    (v : positiveRoot Q split (.inr 3)) :
    ∃ z : CoefficientField m,
      V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
        ((V2Section Q split c).numeratorAction
          (inclusion (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left) (suzukiChart Q split c (a,b)))
          (inclusion (positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide)) v)))) =
      V2Coordinates Q split c (Additive.ofMul (V2ShiftedSuzuki Q split c v)) + ![z,0,0,0] := by
  let u := suzukiChart Q split c (a,b)
  have hc : ⁅(u : X ⧸ Q.D),(v : X ⧸ Q.D)⁆ ∈ positiveRoot Q split (.inl 1) := by
    have he : ⁅simpleRoot Q split 1,positiveRoot Q split (.inr 3)⁆ =
        positiveRoot Q split (.inl 1) := by
      simpa only [nConj,U,Uat,OneMemClass.coe_one,rightConjugate_one,
        positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons]
        using c.relations.ten_two_ii_left 1
    exact he ▸ commutator_mem_commutator u.property v.property
  let w : positiveRoot Q split (.inl 1) := ⟨_,hc⟩
  let y := inclusion (reflectedLinear_le_suzukiRemainder Q split c) w
  let v' := inclusion (positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide)) v
  have hw : (V2Section Q split c).numeratorAction (inclusion (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left) u) v' = y*v' := by
    apply Subtype.ext
    change (u : X ⧸ Q.D)*v*(u : X ⧸ Q.D)⁻¹ =
      ⁅(u : X ⧸ Q.D),(v : X ⧸ Q.D)⁆*v
    simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
  refine ⟨reflectedLinearCoordinate Q split c w,?_⟩
  have hh := congrArg (fun v : (V2Section Q split c).numerator =>
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) hw
  apply hh.trans
  have h := congrArg Multiplicative.toAdd ((V2CoordinateHom Q split c).map_mul y v')
  change V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk (y*v'))) =
    V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c w)) +
      V2Coordinates Q split c (Additive.ofMul (V2ShiftedSuzuki Q split c v)) at h
  rw [V2Coordinates_reflectedLinear] at h
  exact h.trans (add_comm _ _)

private theorem V2Shifted_first_two (v : positiveRoot Q split (.inr 3)) :
    V2Coordinates Q split c (Additive.ofMul (V2ShiftedSuzuki Q split c v)) =
      let x := V2Coordinates Q split c (Additive.ofMul (V2ShiftedSuzuki Q split c v))
      ![x 0,x 1,0,0] := by
  let x := V2Coordinates Q split c (Additive.ofMul (V2ShiftedSuzuki Q split c v))
  obtain ⟨z,hz⟩ := V2_shifted_first_displacement Q split c 1 0 v
  have hz := (V2Coordinates_suzukiChart Q split c 1 0
    (inclusion (positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide)) v)).symm.trans hz
  change (![x 0+1*x 1+(0+1*titsEnd m 1)*x 2+
      (1^2*titsEnd m 1+1*0+titsEnd m 0)*x 3,
      x 1+titsEnd m 1*x 2+0*x 3,x 2+1*x 3,x 3] : Representation.SuzukiNatural.W m) =
    x + ![z,0,0,0] at hz
  have hx3 : x 3 = 0 := by have h := congrFun hz 2; simpa using h
  have hx2 : x 2 = 0 := by have h := congrFun hz 1; simpa using h
  change x = ![x 0,x 1,0,0]
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hx2
  · exact hx3

/-- Reflection exchanges the two literal Suzuki middle representatives. -/
theorem V2Middle_reflection (a : simpleRoot Q split 1) :
    (V2Section Q split c).numeratorAction
      ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
      (inclusion (positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide))
        (positiveRootEquiv Q split c (.inr 3) a)) =
      inclusion (positiveRoot_le_remainder Q split c (.inr 2) 1 (by decide))
        (positiveRootEquiv Q split c (.inr 2) a) := by
  apply Subtype.ext
  change ((c.reflections 1).val : X ⧸ Q.D)*
    ((((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)⁻¹*a*
      (((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val))*
    ((c.reflections 1).val : X ⧸ Q.D)⁻¹ =
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹*a*(c.reflections 0).val
  group

private theorem V2Interior_third_zero (v : (V2Section Q split c).numerator)
    (hv : (v : X ⧸ Q.D) ∈ Set.range (rootProduct (V2InteriorFactors Q split))) :
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v)) 2 = 0 := by
  obtain ⟨⟨a,b,d,e,f,t⟩,hp⟩ := hv
  let a' : (V2Section Q split c).numerator := inclusion (positiveRoot_le_remainder Q split c (.inl 2) 1 (by decide)) a
  let b' : (V2Section Q split c).numerator := inclusion (positiveRoot_le_remainder Q split c (.inr 1) 1 (by decide)) b
  let d' : (V2Section Q split c).numerator := inclusion (positiveRoot_le_remainder Q split c (.inl 3) 1 (by decide)) d
  let e' : (V2Section Q split c).numerator := inclusion (positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide)) e
  let f' : (V2Section Q split c).numerator := inclusion (positiveRoot_le_remainder Q split c (.inl 1) 1 (by decide)) f
  have he : v = a'*b'*d'*e'*f' := by
    apply Subtype.ext
    change (v : X ⧸ Q.D) = (a : X ⧸ Q.D)*b*d*e*f
    simpa only [V2InteriorFactors,rootProduct,mul_one,mul_assoc] using hp.symm
  have ha := V2Coordinates_T2 Q split c a' ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left) (nextLinear_le_phi Q split c a.property))
  have hb := V2Coordinates_T2 Q split c b' ((show perpendicularSuzuki Q split ≤ T2 Q split from le_sup_right) b.property)
  have hd := V2Coordinates_T2 Q split c d' ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left) (perpendicularLinear_le_phi Q split c d.property))
  have hh := congrArg Multiplicative.toAdd (congrArg (V2CoordinateHom Q split c) he)
  simp only [map_mul] at hh
  change V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v)) =
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk a')) +
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk b')) +
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk d')) +
    V2Coordinates Q split c (Additive.ofMul (V2ShiftedSuzuki Q split c e)) +
    V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c f)) at hh
  rw [ha,hb,hd,V2Shifted_first_two,V2Coordinates_reflectedLinear] at hh
  simpa using congrFun hh 2

/-- The shifted root is the second coordinate line also over the binary field.
The reflected displacement bound excludes a tilted first coordinate. -/
theorem pinnedV2_shiftedSuzuki (v : positiveRoot Q split (.inr 3)) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (V2ShiftedSuzuki Q split (pinnedInput Q split c) v)) =
      let x := V2Coordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (V2ShiftedSuzuki Q split (pinnedInput Q split c) v))
      ![0,x 1,0,0] := by
  have hrootLe : simpleRoot Q split 1 ≤ rankOne Q split 1 := le_sup_left
  let d := pinnedInput Q split c
  let x := V2Coordinates Q split d (Additive.ofMul (V2ShiftedSuzuki Q split d v))
  let v' : (V2Section Q split d).numerator :=
    inclusion (positiveRoot_le_remainder Q split d (.inr 3) 1 (by decide)) v
  let w := (V2Section Q split d).numeratorAction
    ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩ v'
  have href : V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) =
      ![x 3,x 2,x 1,x 0] := pinnedV2_reflection Q split c v'
  have hw : (w : X ⧸ Q.D) ∈ positiveRoot Q split (.inr 2) := by
    obtain ⟨a,ha⟩ := (positiveRootEquiv Q split d (.inr 3)).surjective v
    have he := V2Middle_reflection Q split d a
    rw [ha] at he
    have he' : (w : X ⧸ Q.D) = (positiveRootEquiv Q split d (.inr 2) a : X ⧸ Q.D) :=
      congrArg Subtype.val he
    rw [he']
    exact (positiveRootEquiv Q split d (.inr 2) a).property
  let u := suzukiChart Q split d (1,0)
  have hc : ⁅(u : X ⧸ Q.D),(w : X ⧸ Q.D)⁆ ∈
      ⁅simpleRoot Q split 1,positiveRoot Q split (.inr 2)⁆ :=
    commutator_mem_commutator u.property hw
  let z : (V2Section Q split d).numerator :=
    (V2Section Q split d).numeratorAction (inclusion hrootLe u) w * w⁻¹
  have hz : (z : X ⧸ Q.D) = ⁅(u : X ⧸ Q.D),(w : X ⧸ Q.D)⁆ := by
    change (u : X ⧸ Q.D)*w*(u : X ⧸ Q.D)⁻¹*(w : X ⧸ Q.D)⁻¹ = _
    rfl
  have hz2 := V2Interior_third_zero Q split d z (by
    rw [hz]; exact V2_cross_commutator_support Q split d _ hc)
  have hh := congrArg Multiplicative.toAdd ((V2CoordinateHom Q split d).map_mul
    ((V2Section Q split d).numeratorAction (inclusion hrootLe u) w) w⁻¹)
  have hh' := (V2CoordinateHom Q split d).map_inv w
  change (V2CoordinateHom Q split d) w⁻¹ = _ at hh'
  rw [hh'] at hh
  change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk z)) =
    V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk
      ((V2Section Q split d).numeratorAction (inclusion hrootLe u) w))) + -
      V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) at hh
  have hact := congrFun (V2Coordinates_suzukiChart Q split d 1 0 w) 2
  have hw2 := congrFun href 2
  have hw3 := congrFun href 3
  have hx0 : x 0 = 0 := by
    have hh := congrFun hh 2
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk z)) 2 =
      V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk
        ((V2Section Q split d).numeratorAction (inclusion hrootLe u) w))) 2 +
      -(V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) 2) at hh
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk
        ((V2Section Q split d).numeratorAction (inclusion hrootLe u) w))) 2 =
      V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) 2 +
        1*V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) 3 at hact
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) 2 = x 1 at hw2
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) 3 = x 0 at hw3
    rw [hact,hz2,hw2,hw3,one_mul,add_comm (x 1) (x 0),add_assoc,add_neg_cancel,add_zero] at hh
    exact hh.symm
  have he := V2Shifted_first_two Q split d v
  change x = ![x 0,x 1,0,0] at he
  change x = ![0,x 1,0,0]
  simpa only [hx0] using he

/-- The reflected middle root has the third-axis coordinate, with exactly
its second-axis partner's additive label. -/
theorem pinnedV2_oppositeSuzuki (a : simpleRoot Q split 1) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
      (V2OppositeSuzuki Q split (pinnedInput Q split c)
        (positiveRootEquiv Q split (pinnedInput Q split c) (.inr 2) a))) =
      ![0,0,V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
        (V2ShiftedSuzuki Q split (pinnedInput Q split c)
          (positiveRootEquiv Q split (pinnedInput Q split c) (.inr 3) a))) 1,0] := by
  let d := pinnedInput Q split c
  have h := pinnedV2_reflection Q split c
    (inclusion (positiveRoot_le_remainder Q split d (.inr 3) 1 (by decide))
      (positiveRootEquiv Q split d (.inr 3) a))
  have he := congrArg (fun v : (V2Section Q split d).numerator =>
    V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk v)))
    (V2Middle_reflection Q split d a)
  have h := he.symm.trans h
  change V2Coordinates Q split d (Additive.ofMul
    (V2OppositeSuzuki Q split d (positiveRootEquiv Q split d (.inr 2) a))) =
      let x := V2Coordinates Q split d (Additive.ofMul
        (V2ShiftedSuzuki Q split d (positiveRootEquiv Q split d (.inr 3) a)))
      ![x 3,x 2,x 1,x 0] at h
  dsimp only at h
  rw [pinnedV2_shiftedSuzuki] at h
  exact h

private theorem V2Shifted_omega_zero (b : CoefficientField m) :
    V2ShiftedSuzuki Q split c (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (0,b)) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left) (shiftedOmega_le_phi Q split c (shiftedOmegaPoint Q split c b).property)

/-- The second Suzuki parameter vanishes in V₂ through its literal Omega subgroup. -/
theorem V2Shifted_parameter (a b : CoefficientField m) :
    V2ShiftedSuzuki Q split c (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a,b)) =
    V2ShiftedSuzuki Q split c (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a,0)) := by
  have he : positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a,b) =
      positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a,0) *
      positiveChart Q split c (RingEquiv.refl _) (.inr 3) (0,b) := by
    apply Subtype.ext
    change positivePoint Q split c (RingEquiv.refl _) (.inr 3) (a,b) =
      positivePoint Q split c (RingEquiv.refl _) (.inr 3) (a,0) *
      positivePoint Q split c (RingEquiv.refl _) (.inr 3) (0,b)
    simpa only [add_zero,zero_add,mul_zero] using
      (positivePoint_quartet_mul Q split c (RingEquiv.refl _) 3 a 0 0 b).symm
  rw [he,map_mul,V2Shifted_omega_zero,mul_one]

/-- The source quotient U₂^(s₁s₂)/Ω₁ has its actual additive parameter in V₂. -/
def V2MiddleParameter : Multiplicative (CoefficientField m) →* (V2Section Q split c).Carrier where
  toFun a := V2ShiftedSuzuki Q split c (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a.toAdd,0))
  map_one' := by
    have he : positiveChart Q split c (RingEquiv.refl _) (.inr 3) (0,0) = 1 :=
      Subtype.ext (positivePoint_quartet_zero Q split c (RingEquiv.refl _) 3)
    change V2ShiftedSuzuki Q split c (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (0,0)) = 1
    rw [he,map_one]
  map_mul' a b := by
    change V2ShiftedSuzuki Q split c (positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a.toAdd+b.toAdd,0)) = _
    rw [←map_mul]
    have he : positiveChart Q split c (RingEquiv.refl _) (.inr 3) (a.toAdd,0) *
        positiveChart Q split c (RingEquiv.refl _) (.inr 3) (b.toAdd,0) =
        positiveChart Q split c (RingEquiv.refl _) (.inr 3)
          (a.toAdd+b.toAdd,titsEnd m a.toAdd*b.toAdd) := by
      apply Subtype.ext
      change positivePoint Q split c (RingEquiv.refl _) (.inr 3) (a.toAdd,0) *
        positivePoint Q split c (RingEquiv.refl _) (.inr 3) (b.toAdd,0) =
        positivePoint Q split c (RingEquiv.refl _) (.inr 3) (a.toAdd+b.toAdd,titsEnd m a.toAdd*b.toAdd)
      simpa only [zero_add] using positivePoint_quartet_mul Q split c (RingEquiv.refl _) 3 a.toAdd 0 b.toAdd 0
    rw [he]
    exact (V2Shifted_parameter Q split c _ _).symm

/-- Reading the second natural coordinate gives the still unsynchronized
additive field label on the Suzuki quotient. -/
def V2MiddleLabelHom : CoefficientField m →+ CoefficientField m :=
  (Pi.evalAddMonoidHom _ 1).comp
    ((V2Coordinates Q split (pinnedInput Q split c)).toLinearEquiv.toAddMonoidHom.comp
      (V2MiddleParameter Q split (pinnedInput Q split c)).toAdditive)

theorem pinnedV2_shifted_parameter (a b : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
      (V2ShiftedSuzuki Q split (pinnedInput Q split c)
        (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (a,b)))) =
      ![0,V2MiddleLabelHom Q split c a,0,0] := by
  rw [V2Shifted_parameter]
  exact pinnedV2_shiftedSuzuki Q split c _

theorem pinnedV2_opposite_parameter (a b : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
      (V2OppositeSuzuki Q split (pinnedInput Q split c)
        (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 2) (a,b)))) =
      ![0,0,V2MiddleLabelHom Q split c a,0] := by
  have h := pinnedV2_oppositeSuzuki Q split c (suzukiChart Q split (pinnedInput Q split c) (a,b))
  change V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
    (V2OppositeSuzuki Q split (pinnedInput Q split c)
      (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 2) (a,b)))) =
    ![0,0,V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
      (V2ShiftedSuzuki Q split (pinnedInput Q split c)
        (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (a,b)))) 1,0] at h
  rw [pinnedV2_shifted_parameter] at h
  exact h

theorem V2MiddleLabel_surjective : Function.Surjective (V2MiddleLabelHom Q split c) := by
  intro y
  let d := pinnedInput Q split c
  obtain ⟨v,hv⟩ := (V2Coordinates Q split d).surjective ![0,y,0,0]
  obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (V2Section Q split d).denominator v.toMul
  have hw : V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) = ![0,y,0,0] :=
    (congrArg (fun z => V2Coordinates Q split d (Additive.ofMul z)) hw).trans hv
  obtain ⟨p,hp⟩ := (positiveCoordinates Q split d (RingEquiv.refl _)).surjective ⟨w,w.property.1⟩
  have he := (positiveCoordinates_apply Q split d (RingEquiv.refl _) p).symm.trans
    (congrArg Subtype.val hp)
  change CoefficientField m × (CoefficientField m × CoefficientField m) ×
    CoefficientField m × (CoefficientField m × CoefficientField m) × CoefficientField m ×
    (CoefficientField m × CoefficientField m) × CoefficientField m ×
    (CoefficientField m × CoefficientField m) × PUnit at p
  rcases p with ⟨a,b,f,g,h,j,k,l,t⟩
  let a' : (V2Section Q split d).numerator := inclusion (simpleLinear_le_suzukiRemainder Q split d)
    (linearChart Q split d (RingEquiv.refl _) (Multiplicative.ofAdd a))
  let b' : (V2Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inr 2) 1 (by decide))
    (positiveChart Q split d (RingEquiv.refl _) (.inr 2) b)
  let f' : (V2Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inl 2) 1 (by decide))
    (positiveChart Q split d (RingEquiv.refl _) (.inl 2) f)
  let g' : (V2Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inr 1) 1 (by decide))
    (positiveChart Q split d (RingEquiv.refl _) (.inr 1) g)
  let h' : (V2Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inl 3) 1 (by decide))
    (positiveChart Q split d (RingEquiv.refl _) (.inl 3) h)
  let j' : (V2Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inr 3) 1 (by decide))
    (positiveChart Q split d (RingEquiv.refl _) (.inr 3) j)
  let k' : (V2Section Q split d).numerator := inclusion (reflectedLinear_le_suzukiRemainder Q split d)
    (positiveChart Q split d (RingEquiv.refl _) (.inl 1) k)
  let u := suzukiChart Q split d l
  have hp : (a'*b'*f'*g'*h'*j'*k' : simpleRemainder Q split 1) = w := by
    have ha : positivePoint Q split d (RingEquiv.refl _) (.inl 0) a = (a' : X ⧸ Q.D) := by
      change (1 : X ⧸ Q.D)⁻¹ * _ * 1 = _
      simp only [inv_one,one_mul,mul_one]
      rfl
    have hl : positivePoint Q split d (RingEquiv.refl _) (.inr 0) l = (u : X ⧸ Q.D) := by
      change (1 : X ⧸ Q.D)⁻¹ * _ * 1 = _
      simp only [inv_one,one_mul,mul_one]
      rfl
    change positivePoint Q split d (RingEquiv.refl _) (.inl 0) a *
      (positivePoint Q split d (RingEquiv.refl _) (.inr 2) b *
      (positivePoint Q split d (RingEquiv.refl _) (.inl 2) f *
      (positivePoint Q split d (RingEquiv.refl _) (.inr 1) g *
      (positivePoint Q split d (RingEquiv.refl _) (.inl 3) h *
      (positivePoint Q split d (RingEquiv.refl _) (.inr 3) j *
      (positivePoint Q split d (RingEquiv.refl _) (.inl 1) k *
      (positivePoint Q split d (RingEquiv.refl _) (.inr 0) l * 1))))))) = w at he
    rw [ha,hl] at he
    change (a' : X ⧸ Q.D)*((b' : X ⧸ Q.D)*((f' : X ⧸ Q.D)*
      ((g' : X ⧸ Q.D)*((h' : X ⧸ Q.D)*((j' : X ⧸ Q.D)*
      ((k' : X ⧸ Q.D)*((u : X ⧸ Q.D)*1))))))) = w at he
    have hu : (u : X ⧸ Q.D) ∈ simpleRemainder Q split 1 := by
      have hh := (simpleRemainder Q split 1).mul_mem
        ((simpleRemainder Q split 1).inv_mem (a'*b'*f'*g'*h'*j'*k').property) w.property
      rw [←he] at hh
      simpa only [Subgroup.coe_mul,mul_one,mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hh
    have hu1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split 1) u.property hu
    rw [hu1] at he
    apply Subtype.ext
    change (a' : X ⧸ Q.D)*b'*f'*g'*h'*j'*k' = w
    simpa only [mul_one,mul_assoc] using he
  have hf := V2Coordinates_T2 Q split d f'
    ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left) (nextLinear_le_phi Q split d (positiveChart Q split d (RingEquiv.refl _) (.inl 2) f).property))
  have hg := V2Coordinates_T2 Q split d g'
    ((show perpendicularSuzuki Q split ≤ T2 Q split from le_sup_right) (positiveChart Q split d (RingEquiv.refl _) (.inr 1) g).property)
  have hh := V2Coordinates_T2 Q split d h'
    ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left) (perpendicularLinear_le_phi Q split d (positiveChart Q split d (RingEquiv.refl _) (.inl 3) h).property))
  have he := congrArg Multiplicative.toAdd (congrArg (V2CoordinateHom Q split d) hp)
  simp only [map_mul] at he
  change V2Coordinates Q split d (Additive.ofMul (V2SimpleLinear Q split d
      (linearChart Q split d (RingEquiv.refl _) (Multiplicative.ofAdd a)))) +
    V2Coordinates Q split d (Additive.ofMul (V2OppositeSuzuki Q split d
      (positiveChart Q split d (RingEquiv.refl _) (.inr 2) b))) +
    V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk f')) +
    V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk g')) +
    V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk h')) +
    V2Coordinates Q split d (Additive.ofMul (V2ShiftedSuzuki Q split d
      (positiveChart Q split d (RingEquiv.refl _) (.inr 3) j))) +
    V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d
      (positiveChart Q split d (RingEquiv.refl _) (.inl 1) k))) =
      V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) at he
  rw [pinnedV2_simpleLinear,pinnedV2_opposite_parameter Q split c b.1 b.2,hf,hg,hh,
    pinnedV2_shifted_parameter Q split c j.1 j.2,V2Coordinates_reflectedLinear,hw] at he
  exact ⟨j.1,by simpa using congrFun he 1⟩

/-- The two middle roots share an actual additive equivalence of the common field. -/
def V2MiddleFieldLabel : CoefficientField m ≃+ CoefficientField m :=
  AddEquiv.ofBijective (V2MiddleLabelHom Q split c)
    ((Finite.surjective_iff_bijective).mp (V2MiddleLabel_surjective Q split c))

/-- The four literal roots in (10.4), with the same additive label on each
reflected pair, realize an arbitrary natural coordinate vector. -/
def V2NaturalPoint (σ : CoefficientField m ≃+* CoefficientField m)
    (p : Representation.SuzukiNatural.W m) : (V2Section Q split (pinnedInput Q split c)).Carrier :=
  let d := pinnedInput Q split c
  let ℓ := reflectedLinearFieldLabel Q split d σ
  let τ := V2MiddleFieldLabel Q split c
  V2ReflectedLinear Q split d (positiveChart Q split d σ (.inl 1) (ℓ.symm (p 0))) *
    V2ShiftedSuzuki Q split d (positiveChart Q split d (RingEquiv.refl _) (.inr 3) (τ.symm (p 1),0)) *
    V2OppositeSuzuki Q split d (positiveChart Q split d (RingEquiv.refl _) (.inr 2) (τ.symm (p 2),0)) *
    V2SimpleLinear Q split d (linearChart Q split d σ (Multiplicative.ofAdd (ℓ.symm (p 3))))

theorem V2NaturalPoint_coordinates (σ : CoefficientField m ≃+* CoefficientField m)
    (p : Representation.SuzukiNatural.W m) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (V2NaturalPoint Q split c σ p)) = p := by
  let d := pinnedInput Q split c
  let ℓ := reflectedLinearFieldLabel Q split d σ
  let τ := V2MiddleFieldLabel Q split c
  let v₀ := V2ReflectedLinear Q split d (positiveChart Q split d σ (.inl 1) (ℓ.symm (p 0)))
  let v₁ := V2ShiftedSuzuki Q split d (positiveChart Q split d (RingEquiv.refl _) (.inr 3) (τ.symm (p 1),0))
  let v₂ := V2OppositeSuzuki Q split d (positiveChart Q split d (RingEquiv.refl _) (.inr 2) (τ.symm (p 2),0))
  let v₃ := V2SimpleLinear Q split d (linearChart Q split d σ (Multiplicative.ofAdd (ℓ.symm (p 3))))
  have h₀ : V2Coordinates Q split d (Additive.ofMul v₀) = ![p 0,0,0,0] := by
    exact (V2Coordinates_reflectedLinear Q split d _).trans
      (by change ![ℓ (ℓ.symm (p 0)),0,0,0] = _; rw [AddEquiv.apply_symm_apply])
  have h₁ : V2Coordinates Q split d (Additive.ofMul v₁) = ![0,p 1,0,0] := by
    exact (pinnedV2_shifted_parameter Q split c _ _).trans
      (by change ![0,τ (τ.symm (p 1)),0,0] = _; rw [AddEquiv.apply_symm_apply])
  have h₂ : V2Coordinates Q split d (Additive.ofMul v₂) = ![0,0,p 2,0] := by
    exact (pinnedV2_opposite_parameter Q split c _ _).trans
      (by change ![0,0,τ (τ.symm (p 2)),0] = _; rw [AddEquiv.apply_symm_apply])
  have h₃ : V2Coordinates Q split d (Additive.ofMul v₃) = ![0,0,0,p 3] := by
    exact (pinnedV2_simpleLinear Q split c _).trans
      (by change ![0,0,0,ℓ (ℓ.symm (p 3))] = _; rw [AddEquiv.apply_symm_apply])
  change (V2Coordinates Q split d).toLinearEquiv
    (Additive.ofMul v₀+Additive.ofMul v₁+Additive.ofMul v₂+Additive.ofMul v₃) = p
  rw [map_add,map_add,map_add]
  change V2Coordinates Q split d (Additive.ofMul v₀)+V2Coordinates Q split d (Additive.ofMul v₁)+
    V2Coordinates Q split d (Additive.ofMul v₂)+V2Coordinates Q split d (Additive.ofMul v₃) = p
  rw [h₀,h₁,h₂,h₃]
  ext i
  fin_cases i <;> simp

theorem V2NaturalPoint_bijective (σ : CoefficientField m ≃+* CoefficientField m) :
    Function.Bijective (V2NaturalPoint Q split c σ) := by
  constructor
  · intro p q he
    have he := congrArg (fun z => V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul z)) he
    simpa only [V2NaturalPoint_coordinates] using he
  · intro v
    refine ⟨V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul v),?_⟩
    apply (V2Coordinates Q split (pinnedInput Q split c)).injective
    exact V2NaturalPoint_coordinates Q split c σ _

/-- The exact basis shape (1,x,x,1) in (10.4). No field twist is assumed to
be synchronized; both middle entries use the same nonzero source parameter. -/
theorem V2_source_basis (σ : CoefficientField m ≃+* CoefficientField m) :
    ∃ x s : CoefficientField m, x ≠ 0 ∧ s ≠ 0 ∧
      V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
        (V2ReflectedLinear Q split (pinnedInput Q split c)
          (positiveChart Q split (pinnedInput Q split c) σ (.inl 1) 1))) = ![s,0,0,0] ∧
      V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
        (V2ShiftedSuzuki Q split (pinnedInput Q split c)
          (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (x,0)))) = ![0,s,0,0] ∧
      V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
        (V2OppositeSuzuki Q split (pinnedInput Q split c)
          (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 2) (x,0)))) = ![0,0,s,0] ∧
      V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul
        (V2SimpleLinear Q split (pinnedInput Q split c)
          (linearChart Q split (pinnedInput Q split c) σ (Multiplicative.ofAdd 1)))) = ![0,0,0,s] := by
  let d := pinnedInput Q split c
  let s := reflectedLinearFieldLabel Q split d σ 1
  let τ := V2MiddleFieldLabel Q split c
  let x := τ.symm s
  have hs : s ≠ 0 := by
    intro hz
    exact one_ne_zero ((reflectedLinearFieldLabel Q split d σ).injective
      (hz.trans (map_zero _).symm))
  have hx : x ≠ 0 := by
    intro hz
    have h := congrArg τ hz
    change τ (τ.symm s) = τ 0 at h
    rw [AddEquiv.apply_symm_apply,map_zero] at h
    exact hs h
  refine ⟨x,s,hx,hs,V2Coordinates_reflectedLinear Q split d _,?_,?_,pinnedV2_simpleLinear Q split c _⟩
  · exact (pinnedV2_shifted_parameter Q split c x 0).trans
      (by change ![0,τ (τ.symm s),0,0] = _; rw [AddEquiv.apply_symm_apply])
  · exact (pinnedV2_opposite_parameter Q split c x 0).trans
      (by change ![0,0,τ (τ.symm s),0] = _; rw [AddEquiv.apply_symm_apply])

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
