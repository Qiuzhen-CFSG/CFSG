module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiSynchronizedCommutators

/-!
# Synchronizing the two labels on the second Suzuki natural section

The supplied linear reflection compares the third coordinate of Phi with
V2's first coordinate. A vector with last coordinate zero is a product of
its first three root-axis representatives modulo the actual center. After
reflection, the shifted Omega factor, perpendicular linear factor and
center discrepancy all lie in T2; only the next linear root survives.

Apply this comparison to the commutator of the opposite Omega point with
u2(t,0). Its reflection is the inverse of the first-layer commutator of the
opposite Suzuki point with u2(0,y). The two natural actions give
Phi(t*y) = t*Omega(y). Thus both labels are multiplication by the same
scalar. The final two exports apply this identity to the literal source
commutator (10.11)(i), retaining the original quotient, supplied reflections
and binary field.

Source: Fong--Seitz II (1974), (10.9)--(10.11), printed pp.223--224.
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

private def phiReadout : (phiCenterSection Q split c).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((phiCenterCoordinates Q split c).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (phiCenterSection Q split c).denominator)

private def V2Readout : (V2Section Q split c).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((V2Coordinates Q split c).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (V2Section Q split c).denominator)

private theorem V2Readout_T2 (v : (V2Section Q split c).numerator)
    (h : (v : X ⧸ Q.D) ∈ T2 Q split) : V2Readout Q split c v = 1 := by
  change Multiplicative.ofAdd (V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) = 1
  have hv : (QuotientGroup.mk v : (V2Section Q split c).Carrier) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h
  rw [hv]
  exact congrArg Multiplicative.ofAdd ((V2Coordinates Q split c).toLinearEquiv.map_zero)

private theorem linearReflection_root (i : RootPresentationRecognition.PositiveTables.Root) :
    (positiveRoot Q split i).map
      (MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)).toMonoidHom =
      rootAt Q split (positiveKind i)
        (positiveWord (Q.simple 0) (Q.simple 1) i * Q.simple 0) := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  have he : (MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)).symm =
      MulAut.conj ((c.reflections 0).val : X ⧸ Q.D) := by
    ext x
    simp only [MulAut.conj_symm_apply,MulAut.conj_apply,inv_inv]
  rw [he]
  change rightConjugate (positiveRoot Q split i) ((c.reflections 0).val : X ⧸ Q.D) = _
  exact rootAt_right Q split _ _ _ (c.reflections 0).val (c.reflections 0).class_eq

private theorem linearReflection_shiftedOmega (a : omegaOneAmbient (positiveRoot Q split (.inr 3))) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹*a*(c.reflections 0).val ∈
      omegaOneAmbient (positiveRoot Q split (.inr 1)) := by
  let e := MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)
  have h : (omegaOneAmbient (positiveRoot Q split (.inr 3))).map e.toMonoidHom =
      omegaOneAmbient (positiveRoot Q split (.inr 1)) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,linearReflection_root]
    rfl
  have ha := mem_map_of_mem e.toMonoidHom a.property
  rw [h] at ha
  simpa only [e,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using ha

private theorem linearReflection_perpendicularOmega (a : omegaOneAmbient (positiveRoot Q split (.inr 1))) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹*a*(c.reflections 0).val ∈
      omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
  let e := MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)
  have hs : Q.simple 0 * Q.simple 0 = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem 0)).2
  have h : (omegaOneAmbient (positiveRoot Q split (.inr 1))).map e.toMonoidHom =
      omegaOneAmbient (positiveRoot Q split (.inr 3)) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,linearReflection_root]
    simp only [positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,
      mul_assoc,hs,mul_one]
  have ha := mem_map_of_mem e.toMonoidHom a.property
  rw [h] at ha
  simpa only [e,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using ha

private theorem linearReflection_perpendicular (a : positiveRoot Q split (.inl 3)) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹*a*(c.reflections 0).val ∈
      positiveRoot Q split (.inl 3) := by
  have h : (positiveRoot Q split (.inl 3)).map
      (MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)).toMonoidHom =
      positiveRoot Q split (.inl 3) := by
    rw [Subgroup.map_equiv_eq_comap_symm']
    have he : (MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)).symm =
        MulAut.conj ((c.reflections 0).val : X ⧸ Q.D) := by
      ext x
      simp only [MulAut.conj_symm_apply,MulAut.conj_apply,inv_inv]
    rw [he]
    change rightConjugate (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1))
      ((c.reflections 0).val : X ⧸ Q.D) = _
    exact perpendicular_root_stable Q split c.rotation_eight 0 1 (by decide)
      (c.reflections 0).val (c.reflections 0).class_eq
  have ha := mem_map_of_mem
    (MulAut.conj (((c.reflections 0).val : X ⧸ Q.D)⁻¹)).toMonoidHom a.property
  rw [h] at ha
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using ha

private theorem linearReflection_next (a : simpleRoot Q split 0) :
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹ *
      (positiveRootEquiv Q split c (.inl 2) a : X ⧸ Q.D) * (c.reflections 0).val =
      positiveRootEquiv Q split c (.inl 1) a := by
  let s : X ⧸ Q.D := (c.reflections 0).val
  let t : X ⧸ Q.D := (c.reflections 1).val
  have hs : s*s = 1 := linearReflection_sq Q split c
  change s⁻¹*((t*s)⁻¹*(a : X ⧸ Q.D)*(t*s))*s = t⁻¹*a*t
  calc
    _ = (s*s)⁻¹*(t⁻¹*(a : X ⧸ Q.D)*t)*(s*s) := by group
    _ = _ := by rw [hs,inv_one,one_mul,mul_one]

include c in
private theorem perpendicularOmega_le_center : omegaOneAmbient (positiveRoot Q split (.inr 1)) ≤
    zeta (simpleRemainder Q split 1) := by
  have h := c.relations.ten_three_center_remainder 1
  simpa only [nConj,OneMemClass.coe_one,rightConjugate_one,
    Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,
    positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,Uat] using h.le


/-- The supplied linear reflection compares the surviving third Phi axis
with the first V2 axis; the remaining factors lie in T2. -/
private theorem phi_V2_reflection_parameter
    (v : (phiCenterSection Q split (pinnedInput Q split c)).numerator)
    (w : (V2Section Q split (pinnedInput Q split c)).numerator)
    (hv : phiCenterCoordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk v)) 3 = 0)
    (hw : (w : X ⧸ Q.D) = ((c.reflections 0).val : X ⧸ Q.D)⁻¹ * v * (c.reflections 0).val) :
    ∃ z : CoefficientField m,
      synchronizedPhiLabel Q split c z =
        phiCenterCoordinates Q split (pinnedInput Q split c)
          (Additive.ofMul (QuotientGroup.mk v)) 2 ∧
      V2Coordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk w)) 0 = z * pinnedLinearV2Label Q split c 1 := by
  let d := pinnedInput Q split c
  let s : X ⧸ Q.D := (c.reflections 0).val
  let x := phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v))
  let z := (synchronizedPhiLabel Q split c).symm (x 2)
  let a0 := shiftedOmegaPoint Q split d ((shiftedOmegaFieldLabel Q split d).symm (x 0))
  let a1 := synchronizedPositiveChart Q split c (.inl 3)
    ((synchronizedPhiLabel Q split c).symm (x 1))
  let a2 := synchronizedPositiveChart Q split c (.inl 2) z
  let v0 : (phiCenterSection Q split d).numerator := inclusion (shiftedOmega_le_phi Q split d) a0
  let v1 : (phiCenterSection Q split d).numerator := inclusion (perpendicularLinear_le_phi Q split d) a1
  let v2 : (phiCenterSection Q split d).numerator := inclusion (nextLinear_le_phi Q split d) a2
  have h0 : phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v0)) =
      ![x 0,0,0,0] := by
    exact (shiftedOmegaFieldLabel_coordinates Q split d _).trans
      (by rw [AddEquiv.apply_symm_apply])
  have h1 : phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v1)) =
      ![0,x 1,0,0] := by
    exact (synchronizedPhiCoordinates Q split c _).trans
      (by rw [AddEquiv.apply_symm_apply])
  have h2 : phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v2)) =
      ![0,0,x 2,0] := by
    exact (synchronizedPhiNextCoordinates Q split c z).trans
      (by dsimp only [z]; rw [AddEquiv.apply_symm_apply])
  have hp : (QuotientGroup.mk (v0*v1*v2) : (phiCenterSection Q split d).Carrier) =
      QuotientGroup.mk v := by
    apply (phiCenterCoordinates Q split d).injective
    have h' : phiReadout Q split d (v0*v1*v2) =
        phiReadout Q split d v0 * phiReadout Q split d v1 * phiReadout Q split d v2 := by
      simp only [map_mul]
    have h := congrArg Multiplicative.toAdd h'
    change phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk (v0*v1*v2))) =
      phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v0)) +
      phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v1)) +
      phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v2)) at h
    change phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk (v0*v1*v2))) =
      phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v))
    rw [h,h0,h1,h2]
    change _ = x
    ext i
    fin_cases i <;> simp [show x 3 = 0 from hv]
  let k := (v0*v1*v2)⁻¹*v
  have hk : (k : X ⧸ Q.D) ∈ zeta (simpleRemainder Q split 1) := by
    change k ∈ (phiCenterSection Q split d).denominator
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk ((v0*v1*v2)⁻¹*v) : (phiCenterSection Q split d).Carrier) = 1
    rw [QuotientGroup.mk_mul,QuotientGroup.mk_inv,hp,inv_mul_cancel]
  have hkOmega : (k : X ⧸ Q.D) ∈ omegaOneAmbient (positiveRoot Q split (.inr 1)) := by
    have he := d.relations.ten_three_center_remainder 1
    have he' : omegaOneAmbient (positiveRoot Q split (.inr 1)) =
        zeta (simpleRemainder Q split 1) := by
      simpa [nConj,positiveRoot,positiveKind,positiveWord,Uat,
        Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using he
    exact he'.symm ▸ hk
  let w0 : (V2Section Q split d).numerator := ⟨s⁻¹*a0*s,
    (centerRemainder_le_phi Q split d).trans (map_subtype_le _)
      (perpendicularOmega_le_center Q split d (linearReflection_shiftedOmega Q split d a0))⟩
  let w1 : (V2Section Q split d).numerator := ⟨s⁻¹*a1*s,
    (perpendicularLinear_le_phi Q split d).trans (map_subtype_le _)
      (linearReflection_perpendicular Q split d a1)⟩
  let w2 : (V2Section Q split d).numerator := inclusion
    (positiveRoot_le_remainder Q split d (.inl 1) 1 (by decide))
      (synchronizedPositiveChart Q split c (.inl 1) z)
  let wk : (V2Section Q split d).numerator := ⟨s⁻¹*k*s,
    (shiftedOmega_le_phi Q split d).trans (map_subtype_le _)
      (linearReflection_perpendicularOmega Q split d ⟨k,hkOmega⟩)⟩
  have hw0 : V2Readout Q split d w0 = 1 := V2Readout_T2 Q split d w0
    ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
      (centerRemainder_le_phi Q split d
        (perpendicularOmega_le_center Q split d (linearReflection_shiftedOmega Q split d a0))))
  have hw1 : V2Readout Q split d w1 = 1 := V2Readout_T2 Q split d w1
    ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
      (perpendicularLinear_le_phi Q split d (linearReflection_perpendicular Q split d a1)))
  have hwk : V2Readout Q split d wk = 1 := V2Readout_T2 Q split d wk
    ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
      (shiftedOmega_le_phi Q split d (linearReflection_perpendicularOmega Q split d ⟨k,hkOmega⟩)))
  have hw2 : (w2 : X ⧸ Q.D) = s⁻¹*a2*s := by
    exact (linearReflection_next Q split d (synchronizedLinearChart Q split c (.ofAdd z))).symm
  have hwprod : w = w0*w1*w2*wk := by
    apply Subtype.ext
    change (w : X ⧸ Q.D) = (w0 : X ⧸ Q.D)*w1*w2*wk
    rw [hw2]
    change (w : X ⧸ Q.D) = (s⁻¹*v0*s)*(s⁻¹*v1*s)*(s⁻¹*v2*s)*(s⁻¹*((v0*v1*v2)⁻¹*v)*s)
    rw [hw]
    simp only [Subgroup.coe_mul,Subgroup.coe_inv]
    dsimp only [s]
    group
  refine ⟨z,(synchronizedPhiLabel Q split c).apply_symm_apply _,?_⟩
  have hh' := congrArg (V2Readout Q split d) hwprod
  simp only [map_mul,hw0,hw1,hwk,one_mul,mul_one] at hh'
  have hh := congrArg Multiplicative.toAdd hh'
  change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) =
    V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w2)) at hh
  exact (congrFun hh 0).trans (congrFun (synchronized_reflected_coordinates Q split c z) 0)


/-- The reflection comparison in (10.9) identifies the two literal Phi labels. -/
theorem synchronizedPhiLabel_mixed (t y : CoefficientField m) :
    synchronizedPhiLabel Q split c (t*y) = t * shiftedOmegaFieldLabel Q split (pinnedInput Q split c) y := by
  let d := pinnedInput Q split c
  let s : X ⧸ Q.D := (c.reflections 0).val
  let u := suzukiChart Q split d (t,0)
  let o := phiOppositeOmega Q split d y
  let v := phiRightCommutator Q split d u o
  let a := suzukiChart Q split d (0,y)
  let b : (V2Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inr 2) 1 (by decide))
    (synchronizedPositiveChart Q split c (.inr 2) (t,0))
  let w0 := V2RightCommutator Q split d a b
  have hvcoords : phiCenterCoordinates Q split d (Additive.ofMul (QuotientGroup.mk v)) =
      ![(t^2*titsEnd m t)*shiftedOmegaFieldLabel Q split d y,
        (t*titsEnd m t)*shiftedOmegaFieldLabel Q split d y,
        t*shiftedOmegaFieldLabel Q split d y,0] := by
    simpa only [mul_zero,map_zero,add_zero,zero_add] using
      synchronizedPhiOpposite_commutator_coordinates Q split c t 0 y
  have hwcoords : V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w0)) =
      ![y*(t*pinnedLinearV2Label Q split c 1),0,0,0] := by
    have h := V2RightCommutator_coordinates Q split d 0 y b
    dsimp only at h
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w0)) = _ at h
    have hb := synchronized_opposite_coordinates Q split c t 0
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk b)) = _ at hb
    rw [hb] at h
    simpa only [Matrix.cons_val,Fin.isValue,Matrix.head_cons,map_zero,zero_mul,
      mul_zero,zero_add,add_zero] using h
  have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right (linearReflection_sq Q split d)
  have ho : s⁻¹*(o : X ⧸ Q.D)*s = a := by
    rw [show (o : X ⧸ Q.D) = positivePoint Q split d (RingEquiv.refl _) (.inr 2) (0,y)
      from phiOppositeOmega_point Q split d y]
    change s⁻¹*(s⁻¹*(a : X ⧸ Q.D)*s)*s = a
    conv_lhs => arg 1; arg 2; rw [hs]
    conv_lhs => arg 1; arg 2; arg 2; rw [←hs]
    group
  have hu : s⁻¹*(u : X ⧸ Q.D)*s = b := rfl
  have hw : ((w0⁻¹ : (V2Section Q split d).numerator) : X ⧸ Q.D) =
      s⁻¹*(v : X ⧸ Q.D)*s := by
    dsimp only [w0,v]
    rw [Subgroup.coe_inv,V2RightCommutator_val,phiRightCommutator_val]
    rw [←ho,←hu]
    group
  obtain ⟨z,hzphi,hzV2⟩ := phi_V2_reflection_parameter Q split c v w0⁻¹
    (by rw [hvcoords]; rfl) hw
  have hzinv : V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w0⁻¹)) =
      ![y*(t*pinnedLinearV2Label Q split c 1),0,0,0] := by
    rw [QuotientGroup.mk_inv]
    change (V2Coordinates Q split d).toLinearEquiv.toAddEquiv
      (-Additive.ofMul (QuotientGroup.mk w0)) = _
    rw [map_neg]
    change -V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w0)) = _
    rw [hwcoords]
    ext i
    fin_cases i <;> simp [CharTwo.neg_eq]
  have hzy : z = t*y := by
    apply mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    calc
      z*pinnedLinearV2Label Q split c 1 = y*(t*pinnedLinearV2Label Q split c 1) :=
        hzV2.symm.trans (congrFun hzinv 0)
      _ = _ := by ring
  rw [hzy,hvcoords] at hzphi
  exact hzphi

/-- The middle and Omega lines have the same additive label. -/
theorem synchronizedPhiLabel_eq_shiftedOmegaFieldLabel :
    synchronizedPhiLabel Q split c = shiftedOmegaFieldLabel Q split (pinnedInput Q split c) := by
  ext y
  simpa only [one_mul] using synchronizedPhiLabel_mixed Q split c 1 y

/-- The common Phi label is multiplication by one nonzero scalar. -/
theorem synchronizedPhiLabel_scalar (y : CoefficientField m) :
    synchronizedPhiLabel Q split c y =
      y * shiftedOmegaFieldLabel Q split (pinnedInput Q split c) 1 := by
  simpa only [mul_one] using synchronizedPhiLabel_mixed Q split c y 1

/-- The Omega parameters use that same scalar, including q=2. -/
theorem shiftedOmegaFieldLabel_scalar (y : CoefficientField m) :
    shiftedOmegaFieldLabel Q split (pinnedInput Q split c) y =
      y * shiftedOmegaFieldLabel Q split (pinnedInput Q split c) 1 := by
  rw [←synchronizedPhiLabel_eq_shiftedOmegaFieldLabel]
  simpa only [synchronizedPhiLabel_eq_shiftedOmegaFieldLabel] using synchronizedPhiLabel_scalar Q split c y


private theorem synchronizedPhi_inverse (a y : CoefficientField m) :
    (shiftedOmegaFieldLabel Q split (pinnedInput Q split c)).symm
      (a * synchronizedPhiLabel Q split c y) = a*y := by
  apply (shiftedOmegaFieldLabel Q split (pinnedInput Q split c)).injective
  rw [AddEquiv.apply_symm_apply,synchronizedPhiLabel_scalar Q split c y,
    shiftedOmegaFieldLabel_scalar Q split c (a*y),mul_assoc]

/-- Source (10.11)(i) now has the synchronized coefficient a*y in the
actual quotient group, with no remaining additive-label conversion. -/
theorem synchronized_ten_eleven_i (a b y : CoefficientField m) :
    (synchronizedPositivePoint Q split c (.inl 3) y)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 3) y *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) =
      synchronizedPositivePoint Q split c (.inr 3) (0,a*y) := by
  have h := synchronized_perpendicularLinear_right_commutator Q split c a b y
  rw [synchronizedPhi_inverse] at h
  exact h

/-- The same literal equation in Mathlib's commutator convention. -/
theorem synchronized_ten_eleven_i_commutator (a b y : CoefficientField m) :
    ⁅(suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D),
      synchronizedPositivePoint Q split c (.inl 3) y⁆ =
      synchronizedPositivePoint Q split c (.inr 3) (0,a*y) := by
  have h := synchronized_perpendicularLinear_commutator Q split c a b y
  rw [synchronizedPhi_inverse] at h
  exact h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
