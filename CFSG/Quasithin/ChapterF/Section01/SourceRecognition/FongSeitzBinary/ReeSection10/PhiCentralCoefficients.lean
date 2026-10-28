module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiFieldSynchronization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.RankOneCentralization

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

private def phiReadout : (phiCenterSection Q split c).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((phiCenterCoordinates Q split c).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (phiCenterSection Q split c).denominator)

private theorem phiReadout_eq_iff (v w : (phiCenterSection Q split c).numerator) :
    phiReadout Q split c v = phiReadout Q split c w ↔
      (v*w⁻¹ : (phiCenterSection Q split c).numerator) ∈
        (phiCenterSection Q split c).denominator := by
  have h : phiReadout Q split c v = phiReadout Q split c w ↔
      (QuotientGroup.mk v : (phiCenterSection Q split c).Carrier) = QuotientGroup.mk w := by
    constructor
    · intro he
      apply Additive.ofMul.injective
      apply (phiCenterCoordinates Q split c).injective
      exact congrArg Multiplicative.toAdd he
    · intro he
      change Multiplicative.ofAdd (phiCenterCoordinates Q split c (Additive.ofMul
        (QuotientGroup.mk v))) = Multiplicative.ofAdd (phiCenterCoordinates Q split c
          (Additive.ofMul (QuotientGroup.mk w)))
      rw [he]
  rw [h]
  simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem
    (N := (phiCenterSection Q split c).denominator) (x := v) (y := w))

private theorem omega_point_mem (i : Fin 4) (b : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr i) (0,b) ∈
      omegaOneAmbient (positiveRoot Q split (.inr i)) := by
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl _
    (synchronizedPositiveChart Q split c (.inr i) (0,b)).property
  change synchronizedPositivePoint Q split c (.inr i) (0,b) ^ 2 = 1
  rw [pow_two,synchronizedPositivePoint_quartet_mul]
  simpa only [zero_add,map_zero,zero_mul,add_zero,CharTwo.add_self_eq_zero] using
    synchronizedPositivePoint_quartet_zero Q split c i

private def omegaChartHom (i : Fin 4) : Multiplicative (CoefficientField m) →*
    omegaOneAmbient (positiveRoot Q split (.inr i)) where
  toFun a := ⟨synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd),omega_point_mem Q split c i _⟩
  map_one' := Subtype.ext (synchronizedPositivePoint_quartet_zero Q split c i)
  map_mul' a b := by
    apply Subtype.ext
    change synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd+b.toAdd) =
      synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd) *
      synchronizedPositivePoint Q split c (.inr i) (0,b.toAdd)
    symm
    simpa only [zero_add,map_zero,zero_mul,add_zero] using
      synchronizedPositivePoint_quartet_mul Q split c i 0 a.toAdd 0 b.toAdd

private theorem omegaChartHom_bijective (i : Fin 4) : Function.Bijective (omegaChartHom Q split c i) := by
  apply Function.Injective.bijective_of_nat_card_le
  · intro a b h
    have hv : synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd) =
        synchronizedPositivePoint Q split c (.inr i) (0,b.toAdd) :=
      congrArg (fun z : omegaOneAmbient (positiveRoot Q split (.inr i)) => (z : X ⧸ Q.D)) h
    have h' := (synchronizedPositiveChart Q split c (.inr i)).injective (Subtype.ext hv)
    exact Multiplicative.toAdd.injective (congrArg Prod.snd h')
  · rw [omega_positiveRoot_card Q split c i,
      Nat.card_congr Multiplicative.toAdd,GaloisField.card 2 (2*m+1) (by omega)]

include c in
private theorem center_eq_omega : zeta (simpleRemainder Q split 1) =
    omegaOneAmbient (positiveRoot Q split (.inr 1)) := by
  simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,
    Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,
    positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,Uat] using
    (c.relations.ten_three_center_remainder 1).symm

def phiCentralPoint (b : CoefficientField m) :
    (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
  ⟨synchronizedPositivePoint Q split c (.inr 1) (0,b),
    centerRemainder_le_phi Q split (pinnedInput Q split c) (by
      rw [center_eq_omega Q split c]
      exact omega_point_mem Q split c 1 b)⟩

private theorem phiCentralPoint_readout (b : CoefficientField m) :
    phiReadout Q split (pinnedInput Q split c) (phiCentralPoint Q split c b) = 1 := by
  change Multiplicative.ofAdd (phiCenterCoordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (QuotientGroup.mk _))) = 1
  have h : (QuotientGroup.mk (phiCentralPoint Q split c b) :
      (phiCenterSection Q split (pinnedInput Q split c)).Carrier) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    change synchronizedPositivePoint Q split c (.inr 1) (0,b) ∈ zeta _
    rw [center_eq_omega Q split c]
    exact omega_point_mem Q split c 1 b
  rw [h]
  exact congrArg Multiplicative.ofAdd ((phiCenterCoordinates Q split (pinnedInput Q split c)).toLinearEquiv.map_zero)

def phiShiftedPoint (b : CoefficientField m) :
    (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
  inclusion (shiftedOmega_le_phi Q split (pinnedInput Q split c))
    (shiftedOmegaPoint Q split (pinnedInput Q split c) b)

def phiPerpendicularPoint (b : CoefficientField m) :
    (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
  inclusion (perpendicularLinear_le_phi Q split (pinnedInput Q split c))
    (synchronizedPositiveChart Q split c (.inl 3) b)

private theorem phiShiftedPoint_readout (b : CoefficientField m) :
    phiReadout Q split (pinnedInput Q split c) (phiShiftedPoint Q split c b) =
      Multiplicative.ofAdd ![synchronizedPhiLabel Q split c b,0,0,0] := by
  change Multiplicative.ofAdd (phiCenterCoordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (phiShiftedOmega Q split (pinnedInput Q split c)
      (shiftedOmegaPoint Q split (pinnedInput Q split c) b)))) = _
  rw [shiftedOmegaFieldLabel_coordinates,←synchronizedPhiLabel_eq_shiftedOmegaFieldLabel]

private theorem phiPerpendicularPoint_readout (b : CoefficientField m) :
    phiReadout Q split (pinnedInput Q split c) (phiPerpendicularPoint Q split c b) =
      Multiplicative.ofAdd ![0,synchronizedPhiLabel Q split c b,0,0] :=
  congrArg Multiplicative.ofAdd (synchronizedPhiCoordinates Q split c b)

private theorem phiReadout_lift (v w : (phiCenterSection Q split (pinnedInput Q split c)).numerator)
    (h : phiReadout Q split (pinnedInput Q split c) v = phiReadout Q split (pinnedInput Q split c) w) :
    ∃ z : CoefficientField m, v = phiCentralPoint Q split c z * w := by
  have hz := (phiReadout_eq_iff Q split (pinnedInput Q split c) v w).mp h
  change (v : X ⧸ Q.D)*(w : X ⧸ Q.D)⁻¹ ∈ zeta (simpleRemainder Q split 1) at hz
  rw [center_eq_omega Q split c] at hz
  obtain ⟨z,hz⟩ := (omegaChartHom_bijective Q split c 1).surjective ⟨_,hz⟩
  refine ⟨z.toAdd,?_⟩
  apply Subtype.ext
  have hh := congrArg Subtype.val hz
  change synchronizedPositivePoint Q split c (.inr 1) (0,z.toAdd) =
    (v : X ⧸ Q.D)*(w : X ⧸ Q.D)⁻¹ at hh
  change (v : X ⧸ Q.D) = synchronizedPositivePoint Q split c (.inr 1) (0,z.toAdd)*(w : X ⧸ Q.D)
  rw [hh,inv_mul_cancel_right]

/-- Exact lift of (10.11)(ii); the unique central coefficient is still to be computed. -/
theorem synchronized_nextLinear_central_lift (a b y : CoefficientField m) :
    ∃ z : CoefficientField m,
      phiRightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
          (synchronizedPositiveChart Q split c (.inl 2) y)) =
      phiCentralPoint Q split c z *
        (phiShiftedPoint Q split c (b*y) * phiPerpendicularPoint Q split c (titsEnd m a*y)) := by
  apply phiReadout_lift
  rw [map_mul,phiShiftedPoint_readout,phiPerpendicularPoint_readout]
  apply Multiplicative.toAdd.injective
  change phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk _)) =
    ![synchronizedPhiLabel Q split c (b*y),0,0,0] +
      ![0,synchronizedPhiLabel Q split c (titsEnd m a*y),0,0]
  rw [synchronizedPhiNext_commutator_coordinates]
  rw [synchronizedPhiLabel_scalar,synchronizedPhiLabel_scalar,synchronizedPhiLabel_scalar]
  ext i
  fin_cases i <;> simp <;> ring

/-- The Omega actor has no central correction in (10.13)(i). -/
theorem synchronized_nextLinear_omega_commutator (b y : CoefficientField m) :
    (synchronizedPositivePoint Q split c (.inl 2) y)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 2) y *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D) =
      synchronizedPositivePoint Q split c (.inr 3) (0,b*y) := by
  let d := pinnedInput Q split c
  let u := suzukiChart Q split d (0,b)
  let v : (phiCenterSection Q split d).numerator := inclusion (nextLinear_le_phi Q split d) (synchronizedPositiveChart Q split c (.inl 2) y)
  let k := phiRightCommutator Q split d u v
  have hu : ((u : simpleRoot Q split 1) : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split 1) := by
    change (suzukiChart Q split d (0,b) : X ⧸ Q.D) ∈ _
    rw [suzukiChart_apply]
    simp only [zero_mul,add_zero]
    rw [←suzukiOmegaParameter_range Q split 1 m d.suzuki d.suzukiBorel]
    exact ⟨Multiplicative.ofAdd b,rfl⟩
  have hs : ⁅omegaOneAmbient (simpleRoot Q split 1),positiveRoot Q split (.inl 2)⁆ ≤
      omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
    simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,U,Uat,
      positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,
      Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using d.relations.ten_two_v 1
  have hk : (k : X ⧸ Q.D) ∈ omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
    have h := hs (commutator_mem_commutator (inv_mem hu)
      (inv_mem (synchronizedPositiveChart Q split c (.inl 2) y).property))
    rw [commutatorElement_def] at h
    have he : (k : X ⧸ Q.D) =
        ((u : X ⧸ Q.D)⁻¹*(synchronizedPositivePoint Q split c (.inl 2) y)⁻¹*
          (u : X ⧸ Q.D)*(synchronizedPositivePoint Q split c (.inl 2) y))⁻¹ := by
      change (phiRightCommutator Q split d u v : X ⧸ Q.D) = _
      rw [phiRightCommutator_val]
      change (synchronizedPositivePoint Q split c (.inl 2) y)⁻¹ * (u : X ⧸ Q.D)⁻¹ *
        synchronizedPositivePoint Q split c (.inl 2) y * u = _
      group
    rw [he]
    simp only [inv_inv] at h
    change ((u : X ⧸ Q.D)⁻¹ * (synchronizedPositivePoint Q split c (.inl 2) y)⁻¹ *
      u * synchronizedPositivePoint Q split c (.inl 2) y) ∈
      omegaOneAmbient (positiveRoot Q split (.inr 3)) at h
    exact inv_mem h
  have hcoords := synchronizedPhiNext_commutator_coordinates Q split c 0 b y
  have he : phiShiftedOmega Q split d ⟨k,hk⟩ =
      phiShiftedOmega Q split d (shiftedOmegaPoint Q split d (b*y)) := by
    apply (phiCenterCoordinates Q split d).injective
    change phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk k)) =
      phiCenterCoordinates Q split d (Additive.ofMul
        (phiShiftedOmega Q split d (shiftedOmegaPoint Q split d (b*y))))
    rw [hcoords,shiftedOmegaFieldLabel_coordinates,←synchronizedPhiLabel_eq_shiftedOmegaFieldLabel,
      synchronizedPhiLabel_scalar,synchronizedPhiLabel_scalar,map_zero,zero_mul]
    ext i
    fin_cases i <;> simp [mul_assoc]
  have hval := congrArg Subtype.val (phiShiftedOmega_injective Q split d he)
  exact (phiRightCommutator_val Q split d u v).symm.trans hval

private theorem synchronized_omega_central_lift (b y : CoefficientField m) :
    ∃ z : CoefficientField m,
      phiRightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (0,b))
        (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiCentralPoint Q split c z *
        (phiShiftedPoint Q split c (titsEnd m b*y) * phiPerpendicularPoint Q split c (b*y)) := by
  apply phiReadout_lift
  rw [map_mul,phiShiftedPoint_readout,phiPerpendicularPoint_readout]
  apply Multiplicative.toAdd.injective
  change phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk _)) =
    ![synchronizedPhiLabel Q split c (titsEnd m b*y),0,0,0] +
      ![0,synchronizedPhiLabel Q split c (b*y),0,0]
  rw [synchronizedPhiOpposite_commutator_coordinates,
    ←synchronizedPhiLabel_eq_shiftedOmegaFieldLabel]
  rw [synchronizedPhiLabel_scalar,synchronizedPhiLabel_scalar,synchronizedPhiLabel_scalar]
  ext i
  fin_cases i <;> simp <;> ring

private theorem reflect_shifted (b : CoefficientField m) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
      (phiShiftedPoint Q split c b : X ⧸ Q.D) * (c.reflections 0).val =
      phiCentralPoint Q split c b := by
  change ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
    ((((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D) *
      (((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)) * (c.reflections 0).val =
    ((((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)*(c.reflections 0).val)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D) *
      ((((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)*(c.reflections 0).val)
  group

private theorem reflect_central (b : CoefficientField m) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
      (phiCentralPoint Q split c b : X ⧸ Q.D) * (c.reflections 0).val =
      phiShiftedPoint Q split c b := by
  rw [←reflect_shifted Q split c b]
  have hs := linearReflection_sq Q split c
  calc
    _ = (((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 0).val)⁻¹ *
      (phiShiftedPoint Q split c b : X ⧸ Q.D) *
      (((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 0).val) := by group
    _ = _ := by rw [hs,inv_one,one_mul,mul_one]

private theorem reflect_perpendicular (b : CoefficientField m) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
      (phiPerpendicularPoint Q split c b : X ⧸ Q.D) * (c.reflections 0).val =
      phiPerpendicularPoint Q split c b := by
  have hc := mem_centralizer_iff.mp
    (rankOne_centralizes_perpendicularLinear Q split c (c.reflections 0).mem_rankOne)
    (synchronizedPositivePoint Q split c (.inl 3) b)
    (synchronizedPositiveChart Q split c (.inl 3) b).property
  change ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
    synchronizedPositivePoint Q split c (.inl 3) b * (c.reflections 0).val = _
  rw [mul_assoc,hc,inv_mul_cancel_left]
  rfl

private theorem reflect_simple (b : CoefficientField m) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D) * (c.reflections 0).val =
      phiOppositeOmega Q split (pinnedInput Q split c) b := by
  rw [phiOppositeOmega_point]
  rfl

private theorem reflect_opposite (b : CoefficientField m) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
      (phiOppositeOmega Q split (pinnedInput Q split c) b : X ⧸ Q.D) * (c.reflections 0).val =
      suzukiChart Q split (pinnedInput Q split c) (0,b) := by
  rw [←reflect_simple Q split c b]
  have hs := linearReflection_sq Q split c
  calc
    _ = (((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 0).val)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D) *
      (((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 0).val) := by group
    _ = _ := by rw [hs,inv_one,one_mul,mul_one]

/-- The central coefficient in (10.13)(ii), including the binary field. -/
theorem synchronized_omega_omega_commutator (b y : CoefficientField m) :
    phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (0,b))
      (phiOppositeOmega Q split (pinnedInput Q split c) y) =
    phiCentralPoint Q split c (b*titsEnd m y) *
      (phiShiftedPoint Q split c (titsEnd m b*y) * phiPerpendicularPoint Q split c (b*y)) := by
  obtain ⟨z,hz⟩ := synchronized_omega_central_lift Q split c b y
  let d := pinnedInput Q split c
  let k := phiRightCommutator Q split d (suzukiChart Q split d (0,y))
    (phiOppositeOmega Q split d b)
  let r := MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)
  have hr (x : X ⧸ Q.D) : r x = ((c.reflections 0).val : X ⧸ Q.D)⁻¹*x*(c.reflections 0).val := by
    simp only [r,MulAut.conj_apply,inv_inv]
  have he := congrArg (fun v : (phiCenterSection Q split d).numerator => r (v : X ⧸ Q.D)) hz
  change r (phiRightCommutator Q split d (suzukiChart Q split d (0,b))
    (phiOppositeOmega Q split d y) : X ⧸ Q.D) =
    r ((phiCentralPoint Q split c z : X ⧸ Q.D) *
      ((phiShiftedPoint Q split c (titsEnd m b*y) : X ⧸ Q.D) *
        (phiPerpendicularPoint Q split c (b*y) : X ⧸ Q.D))) at he
  rw [phiRightCommutator_val] at he
  simp only [map_mul,map_inv] at he
  dsimp only [d] at he
  simp only [hr,reflect_simple,reflect_opposite,reflect_central,
    reflect_shifted,reflect_perpendicular] at he
  have hk : (k⁻¹ : (phiCenterSection Q split d).numerator) =
      phiShiftedPoint Q split c z *
        (phiCentralPoint Q split c (titsEnd m b*y) * phiPerpendicularPoint Q split c (b*y)) := by
    apply Subtype.ext
    change (k : X ⧸ Q.D)⁻¹ = _
    dsimp only [k]
    rw [phiRightCommutator_val]
    calc
      _ = (suzukiChart Q split d (0,y) : X ⧸ Q.D)⁻¹ *
        (phiOppositeOmega Q split d b : X ⧸ Q.D)⁻¹ *
        (suzukiChart Q split d (0,y) : X ⧸ Q.D) *
        (phiOppositeOmega Q split d b : X ⧸ Q.D) := by group
      _ = _ := he
  have hc := congrArg (phiReadout Q split d) hk
  rw [map_inv,map_mul,map_mul,phiShiftedPoint_readout,
    phiCentralPoint_readout,phiPerpendicularPoint_readout,one_mul] at hc
  have hcoord := congrArg (fun v : Multiplicative (Representation.SuzukiNatural.W m) => v.toAdd 0) hc
  change -(phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk k)) 0) =
    synchronizedPhiLabel Q split c z + 0 at hcoord
  dsimp only [k] at hcoord
  rw [synchronizedPhiOpposite_commutator_coordinates,
    ←synchronizedPhiLabel_eq_shiftedOmegaFieldLabel] at hcoord
  simp only [map_zero,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_add,Matrix.cons_val,
    Fin.isValue,add_zero,CharTwo.neg_eq] at hcoord
  have hz' : z = b*titsEnd m y := by
    apply (synchronizedPhiLabel Q split c).injective
    rw [←hcoord,synchronizedPhiLabel_scalar,synchronizedPhiLabel_scalar]
    ring
  simpa only [hz'] using hz


private def phiDisplacement (u : simpleRoot Q split 1) :
    (phiCenterSection Q split c).numerator →* (phiCenterSection Q split c).numerator := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split c).numerator := phiRemainder_elementary Q split c
  exact {
    toFun := phiRightCommutator Q split c u
    map_one' := by simp [phiRightCommutator]
    map_mul' := by
      intro v w
      simp only [phiRightCommutator,mul_inv_rev,map_mul]
      ac_rfl }

private theorem phiDisplacement_square (u : simpleRoot Q split 1)
    (v : (phiCenterSection Q split c).numerator) :
    phiDisplacement Q split c u (phiDisplacement Q split c u v) =
      phiDisplacement Q split c (u*u) v := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split c).numerator := phiRemainder_elementary Q split c
  let A := (phiCenterSection Q split c).numeratorAction (inclusion le_sup_left u⁻¹)
  have hs (w : (phiCenterSection Q split c).numerator) : w*w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (phiCenterSection Q split c).numerator) w
  have hinv (w : (phiCenterSection Q split c).numerator) : w⁻¹ = w :=
    inv_eq_of_mul_eq_one_right (hs w)
  have hA : (phiCenterSection Q split c).numeratorAction (inclusion le_sup_left (u*u)⁻¹) v = A (A v) := by
    rw [mul_inv_rev,map_mul,map_mul]
    rfl
  change (v⁻¹*A v)⁻¹ * A (v⁻¹*A v) = v⁻¹ * _
  rw [hA,hinv,hinv,map_mul]
  calc
    _ = v * (A v*A v) * A (A v) := by ac_rfl
    _ = _ := by rw [hs,mul_one]

def phiNextPoint (y : CoefficientField m) :
    (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
  inclusion (nextLinear_le_phi Q split (pinnedInput Q split c))
    (synchronizedPositiveChart Q split c (.inl 2) y)

private theorem phiNextPoint_readout (b : CoefficientField m) :
    phiReadout Q split (pinnedInput Q split c) (phiNextPoint Q split c b) =
      Multiplicative.ofAdd ![0,0,synchronizedPhiLabel Q split c b,0] :=
  congrArg Multiplicative.ofAdd (synchronizedPhiNextCoordinates Q split c b)

private theorem synchronized_opposite_central_lift (a b y : CoefficientField m) :
    ∃ z : CoefficientField m,
      phiRightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiCentralPoint Q split c z *
        (phiShiftedPoint Q split c ((a^2*titsEnd m a+a*b+titsEnd m b)*y) *
          phiPerpendicularPoint Q split c ((b+a*titsEnd m a)*y) * phiNextPoint Q split c (a*y)) := by
  apply phiReadout_lift
  rw [map_mul,map_mul,phiShiftedPoint_readout,phiPerpendicularPoint_readout,phiNextPoint_readout]
  apply Multiplicative.toAdd.injective
  change phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk _)) =
    (![synchronizedPhiLabel Q split c ((a^2*titsEnd m a+a*b+titsEnd m b)*y),0,0,0] +
      ![0,synchronizedPhiLabel Q split c ((b+a*titsEnd m a)*y),0,0]) +
      ![0,0,synchronizedPhiLabel Q split c (a*y),0]
  rw [synchronizedPhiOpposite_commutator_coordinates,
    ←synchronizedPhiLabel_eq_shiftedOmegaFieldLabel]
  simp only [synchronizedPhiLabel_scalar]
  ext i
  fin_cases i <;> simp <;> ring

/-- The opposite-Omega commutator has the four noncentral Phi coordinates shown
in (10.11)(iii); only its central Omega factor remains to be identified. -/
theorem synchronized_opposite_central_lift_public (a b y : CoefficientField m) :
    ∃ z : CoefficientField m,
      phiRightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiCentralPoint Q split c z *
        (phiShiftedPoint Q split c ((a^2*titsEnd m a+a*b+titsEnd m b)*y) *
          phiPerpendicularPoint Q split c ((b+a*titsEnd m a)*y) * phiNextPoint Q split c (a*y)) :=
  synchronized_opposite_central_lift Q split c a b y

private theorem phiDisplacement_central (u : simpleRoot Q split 1) (y : CoefficientField m) :
    phiDisplacement Q split (pinnedInput Q split c) u (phiCentralPoint Q split c y) = 1 := by
  have hc := mem_centralizer_iff.mp
    (rankOne_centralizes_perpendicularSuzuki Q split c (show (u : X ⧸ Q.D) ∈ rankOne Q split 1 from
      (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left) u.property))
    (synchronizedPositivePoint Q split c (.inr 1) (0,y))
    (synchronizedPositiveChart Q split c (.inr 1) (0,y)).property
  apply Subtype.ext
  change (phiRightCommutator Q split (pinnedInput Q split c) u _ : X ⧸ Q.D) = 1
  rw [phiRightCommutator_val]
  change (synchronizedPositivePoint Q split c (.inr 1) (0,y))⁻¹ * (u : X ⧸ Q.D)⁻¹ *
    synchronizedPositivePoint Q split c (.inr 1) (0,y) * u = 1
  rw [mul_assoc,hc]
  group

private theorem phiDisplacement_shifted (u : simpleRoot Q split 1) (y : CoefficientField m) :
    phiDisplacement Q split (pinnedInput Q split c) u (phiShiftedPoint Q split c y) = 1 := by
  have hc := mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (shiftedOmega_centralizes_suzukiRoot Q split c) (omega_point_mem Q split c 3 y)) _ u.property
  apply Subtype.ext
  change (phiRightCommutator Q split (pinnedInput Q split c) u _ : X ⧸ Q.D) = 1
  rw [phiRightCommutator_val]
  change (synchronizedPositivePoint Q split c (.inr 3) (0,y))⁻¹ * (u : X ⧸ Q.D)⁻¹ *
    synchronizedPositivePoint Q split c (.inr 3) (0,y) * u = 1
  rw [mul_assoc,←hc]
  group

private theorem phiDisplacement_perpendicular (a b y : CoefficientField m) :
    phiDisplacement Q split (pinnedInput Q split c) (suzukiChart Q split (pinnedInput Q split c) (a,b))
      (phiPerpendicularPoint Q split c y) = phiShiftedPoint Q split c (a*y) := by
  apply Subtype.ext
  change (phiRightCommutator Q split (pinnedInput Q split c) _ _ : X ⧸ Q.D) = _
  rw [phiRightCommutator_val]
  exact synchronized_ten_eleven_i Q split c a b y


private theorem suzukiChart_square (a b : CoefficientField m) :
    suzukiChart Q split c (a,b) * suzukiChart Q split c (a,b) =
      suzukiChart Q split c (0,a*titsEnd m a) := by
  rw [suzukiChart_mul,CharTwo.add_self_eq_zero,CharTwo.add_self_eq_zero,zero_add,mul_comm (titsEnd m a) a]

private theorem phiCentralPoint_injective : Function.Injective (phiCentralPoint Q split c) := by
  intro a b h
  have hh := congrArg (fun v : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    (v : X ⧸ Q.D)) h
  have he := (synchronizedPositiveChart Q split c (.inr 1)).injective (Subtype.ext hh)
  exact congrArg Prod.snd he

private theorem phiDisplacement_next_scaled (a b y : CoefficientField m) :
    phiDisplacement Q split (pinnedInput Q split c) (suzukiChart Q split (pinnedInput Q split c) (a,b))
      (phiNextPoint Q split c (a*y)) =
    phiCentralPoint Q split c (a*titsEnd m (a*y)) *
      (phiShiftedPoint Q split c (b*(a*y)) * phiPerpendicularPoint Q split c (titsEnd m a*(a*y))) := by
  let d := pinnedInput Q split c
  let u := suzukiChart Q split d (a,b)
  let D := phiDisplacement Q split d u
  let : IsElementaryAbelian 2 (phiCenterSection Q split d).numerator := phiRemainder_elementary Q split d
  obtain ⟨z,hz⟩ := synchronized_opposite_central_lift Q split c a b y
  have hh := congrArg D hz
  change D (D (phiOppositeOmega Q split d y)) = _ at hh
  rw [phiDisplacement_square,suzukiChart_square] at hh
  change phiRightCommutator Q split d (suzukiChart Q split d (0,a*titsEnd m a))
    (phiOppositeOmega Q split d y) = _ at hh
  dsimp only [d] at hh
  rw [synchronized_omega_omega_commutator] at hh
  change _ = D (phiCentralPoint Q split c z *
    (phiShiftedPoint Q split c ((a^2*titsEnd m a+a*b+titsEnd m b)*y) *
      phiPerpendicularPoint Q split c ((b+a*titsEnd m a)*y) * phiNextPoint Q split c (a*y))) at hh
  simp only [map_mul] at hh
  dsimp only [D,u] at hh
  rw [phiDisplacement_central,phiDisplacement_shifted,phiDisplacement_perpendicular,
    one_mul,one_mul] at hh
  obtain ⟨w,hw⟩ := synchronized_nextLinear_central_lift Q split c a b (a*y)
  change D (phiNextPoint Q split c (a*y)) = _ at hw
  change _ = phiShiftedPoint Q split c (a*((b+a*titsEnd m a)*y)) *
    D (phiNextPoint Q split c (a*y)) at hh
  rw [hw] at hh
  have hcentral : a*titsEnd m a*titsEnd m y = w := by
    apply phiCentralPoint_injective Q split c
    have hs (x t : CoefficientField m) :
        phiShiftedPoint Q split c x * phiShiftedPoint Q split c t =
          phiShiftedPoint Q split c (x+t) := by
      apply Subtype.ext
      change synchronizedPositivePoint Q split c (.inr 3) (0,x) *
        synchronizedPositivePoint Q split c (.inr 3) (0,t) = _
      change _ = synchronizedPositivePoint Q split c (.inr 3) (0,x+t)
      simpa only [zero_add,map_zero,zero_mul,add_zero] using
        (synchronizedPositivePoint_quartet_mul Q split c 3 0 x 0 t).trans rfl
    have hreorder : phiShiftedPoint Q split c (a*((b+a*titsEnd m a)*y)) *
        (phiCentralPoint Q split c w *
          (phiShiftedPoint Q split c (b*(a*y)) * phiPerpendicularPoint Q split c (titsEnd m a*(a*y)))) =
        phiCentralPoint Q split c w *
          (phiShiftedPoint Q split c (a*((b+a*titsEnd m a)*y)+b*(a*y)) *
            phiPerpendicularPoint Q split c (titsEnd m a*(a*y))) := by
      rw [←hs]
      ac_rfl
    rw [hreorder] at hh
    have ht : titsEnd m (a*titsEnd m a) = titsEnd m a * a^2 := by
      rw [map_mul,titsEnd_twice]
    have h1 : a*((b+a*titsEnd m a)*y)+b*(a*y) = titsEnd m (a*titsEnd m a)*y := by
      rw [ht]
      calc
        _ = (a*b*y + a*b*y) + a^2 * titsEnd m a * y := by ring
        _ = a^2 * titsEnd m a * y := by
          simp only [CharTwo.add_self_eq_zero, zero_add]
        _ = titsEnd m a * a^2 * y := by rw [pow_two]; ac_rfl
    have h2 : a*titsEnd m a*y = titsEnd m a*(a*y) := by ring
    rw [h1,h2] at hh
    have harg : titsEnd m a * titsEnd m (titsEnd m a) * y =
        titsEnd m (a*titsEnd m a) * y := by rw [map_mul]
    rw [harg] at hh
    have hh' : phiCentralPoint Q split c (a*titsEnd m a*titsEnd m y) *
        (phiShiftedPoint Q split c (titsEnd m (a*titsEnd m a)*y) *
          phiPerpendicularPoint Q split c (titsEnd m a*(a*y))) =
        phiCentralPoint Q split c w *
        (phiShiftedPoint Q split c (titsEnd m (a*titsEnd m a)*y) *
          phiPerpendicularPoint Q split c (titsEnd m a*(a*y))) := by simpa only [mul_assoc] using hh
    exact mul_right_cancel hh' 
  rw [←hcentral] at hw
  simpa only [map_mul,mul_assoc] using hw

/-- The complete central coefficient g in (10.15), including q = 2. -/
theorem synchronized_nextLinear_commutator (a b y : CoefficientField m) :
    phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b)) (phiNextPoint Q split c y) =
    phiCentralPoint Q split c (a*titsEnd m y) *
      (phiShiftedPoint Q split c (b*y) * phiPerpendicularPoint Q split c (titsEnd m a*y)) := by
  by_cases ha : a = 0
  · subst a
    apply Subtype.ext
    rw [phiRightCommutator_val]
    change (synchronizedPositivePoint Q split c (.inl 2) y)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 2) y *
      (suzukiChart Q split (pinnedInput Q split c) (0,b) : X ⧸ Q.D) = _
    rw [synchronized_nextLinear_omega_commutator]
    simp only [zero_mul,map_zero]
    change _ = synchronizedPositivePoint Q split c (.inr 1) (0,0) *
      (synchronizedPositivePoint Q split c (.inr 3) (0,b*y) *
        synchronizedPositivePoint Q split c (.inl 3) 0)
    rw [synchronizedPositivePoint_quartet_zero,synchronizedPositivePoint_pair_zero,one_mul,mul_one]
  · have h := phiDisplacement_next_scaled Q split c a b (a⁻¹*y)
    change phiDisplacement Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b)) (phiNextPoint Q split c y) = _
    simpa only [←mul_assoc,mul_inv_cancel₀ ha,one_mul] using h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
