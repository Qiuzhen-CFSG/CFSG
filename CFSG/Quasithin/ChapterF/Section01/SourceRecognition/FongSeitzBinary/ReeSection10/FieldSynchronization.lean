module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V1Basis
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V2Commutators

/-!
# Synchronizing the linear and first Suzuki natural layers

An element in the intersection of the two literal radicals has one leading
Suzuki-root parameter. Carter coordinates remove its terminal root; the
five interior factors are invisible both in V₁ and in V₂'s third coordinate.
Apply this to the same mixed commutator, computed by the two natural actions.
If lambda is the normalized V₁ label, tau the middle V₂ label, and ell the
linear V₂ label, the comparison reads lambda(z)=t lambda(a), tau(z)=a ell(t).
Taking t=1 and a=1 gives tau(a)=a ell(1), ell(t)=lambda⁻¹(t) ell(1).
The general comparison then forces lambda to preserve multiplication.

Thus the relabeled whole linear root has the same field parameter as both
Suzuki middle roots. The supplied reflections, literal quotient and native
Suzuki correction remain fixed, including q=2. SynchronizedCommutators uses
these identities in (10.7)--(10.8); no field compatibility is an input field.
Source: Fong--Seitz II (1974), printed p.223, the comparison after (10.6).
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

/-- The common leading root of the two literal radicals has one source parameter. -/
theorem V1_V2_common_parameter
    (v : (V1Section Q split (pinnedInput Q split c)).numerator)
    (w : (V2Section Q split (pinnedInput Q split c)).numerator)
    (hvw : (v : X ⧸ Q.D) = w) :
    ∃ a : CoefficientField m,
      V1BasisCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)) =
        ![V1BasisLabel Q split (pinnedInput Q split c) a,0] ∧
      V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk w)) 2 =
        V2MiddleFieldLabel Q split c a := by
  let d := pinnedInput Q split c
  have hp : (v : X ⧸ Q.D) ∈ Set.range (rootProduct (linearFactors Q split)) :=
    (linearProduct_range Q split d).symm ▸ v.property
  obtain ⟨⟨a,b,e,f,g,h,k,u⟩,hp⟩ := hp
  let t := rootProduct (V2InteriorFactors Q split) (b,e,f,g,h,u)
  have ht : t ∈ T1 Q split := by
    rw [T1_eq_linearInterior Q split d]
    change t ∈ (linearInterior Q split d : Set (X ⧸ Q.D))
    rw [←interiorProduct_range Q split d]
    exact ⟨(b,e,f,g,h,u),rfl⟩
  have ht2 : t ∈ simpleRemainder Q split 1 :=
    ((T1_eq_linearInterior Q split d).le ht).1.2
  have he : (a : X ⧸ Q.D)*t*k = v := by
    simpa only [t,linearFactors,V2InteriorFactors,rootProduct,mul_one,mul_assoc] using hp
  have hk2 : (k : X ⧸ Q.D) ∈ simpleRemainder Q split 1 := by
    have hh := (simpleRemainder Q split 1).mul_mem
      ((simpleRemainder Q split 1).inv_mem ((simpleRemainder Q split 1).mul_mem
        (positiveRoot_le_remainder Q split d (.inr 2) 1 (by decide) a.property) ht2)) w.property
    rw [←hvw,←he,inv_mul_cancel_left] at hh
    exact hh
  have hk : (k : X ⧸ Q.D) = 1 := disjoint_def.mp
    (simpleRoot_disjoint_remainder Q split 1)
    (by simpa only [positiveRoot,positiveKind,positiveWord,Matrix.cons_val_zero,rootAt_one] using k.property) hk2
  rw [hk,mul_one] at he
  obtain ⟨⟨α,β⟩,ha⟩ := (positiveChart Q split d (RingEquiv.refl _) (.inr 2)).surjective a
  obtain ⟨⟨γ,δ⟩,hg⟩ := (positiveChart Q split d (RingEquiv.refl _) (.inr 3)).surjective g
  let t₁ : (V1Section Q split d).numerator := ⟨t,T1_le_linearRemainder Q split d ht⟩
  let t₂ : (V2Section Q split d).numerator := ⟨t,ht2⟩
  let a₁ : (V1Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inr 2) 0 (by decide)) a
  let a₂ : (V2Section Q split d).numerator := inclusion (positiveRoot_le_remainder Q split d (.inr 2) 1 (by decide)) a
  have hv : v = a₁*t₁ := Subtype.ext he.symm
  have hw : w = a₂*t₂ := Subtype.ext (hvw.symm.trans he.symm)
  have ht₁ : (QuotientGroup.mk t₁ : (V1Section Q split d).Carrier) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ((show T1 Q split ≤ X1 Q split from le_sup_right.trans le_sup_left) ht)
  have ht₂ := V2_interior_coordinates Q split c b e f γ δ h t₂ (by
    change (t : X ⧸ Q.D) = _
    rw [show positivePoint Q split d (RingEquiv.refl _) (.inr 3) (γ,δ) = (g : X ⧸ Q.D) from congrArg Subtype.val hg]
    simp only [t,V2InteriorFactors,rootProduct,mul_one,mul_assoc])
  refine ⟨α,?_,?_⟩
  · have hq : (QuotientGroup.mk v : (V1Section Q split d).Carrier) = QuotientGroup.mk a₁ := by
      rw [hv,QuotientGroup.mk_mul,ht₁,mul_one]
    rw [hq]
    change V1BasisCoordinates Q split d (Additive.ofMul (QuotientGroup.mk
      (inclusion (positiveRoot_le_remainder Q split d (.inr 2) 0 (by decide)) a))) = _
    rw [←ha]
    exact V1BasisCoordinates_shiftedSuzukiChart Q split d α β
  · have hq : (QuotientGroup.mk w : (V2Section Q split d).Carrier) =
        QuotientGroup.mk a₂ * QuotientGroup.mk t₂ := by rw [hw,QuotientGroup.mk_mul]
    rw [hq]
    change (V2Coordinates Q split d).toLinearEquiv
      (Additive.ofMul (QuotientGroup.mk a₂)+Additive.ofMul (QuotientGroup.mk t₂)) 2 = _
    rw [map_add]
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk a₂)) 2 +
      V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk t₂)) 2 = _
    rw [ht₂]
    change V2Coordinates Q split d (Additive.ofMul (V2OppositeSuzuki Q split d a)) 2 + 0 = _
    rw [←ha,pinnedV2_opposite_parameter,add_zero]
    rfl


/-- The actual simple-root chart of the whole reflection-aligned linear pinning. -/
def linearPinnedChart : Multiplicative (CoefficientField m) ≃* simpleRoot Q split 0 :=
  (MonoidHom.ofInjective (GTwoSource.alignedSimpleParameter_injective Q split 0
    (linearRemainder_le_kernel Q split c) (linearLocalMarking Q split c) (c.reflections 0))).trans
      (MulEquiv.subgroupCongr (GTwoSource.alignedSimpleParameter_range Q split 0
        (linearRemainder_le_kernel Q split c) (linearLocalMarking Q split c) (c.reflections 0)))

@[simp] theorem linearPinnedChart_coe (t : CoefficientField m) :
    (linearPinnedChart Q split c (.ofAdd t) : X ⧸ Q.D) =
      (linearPinning Q split c (Theory.PSL2.SemilinearCoverage.uni t) : X ⧸ Q.D) := rfl

theorem linearPinnedChart_inv (t : CoefficientField m) :
    (linearPinnedChart Q split c (.ofAdd t))⁻¹ = linearPinnedChart Q split c (.ofAdd t) := by
  rw [←map_inv]
  congr 1
  exact CharTwo.neg_eq t

/-- The fourth V₂ coordinate on the same reflection-aligned linear chart. -/
def pinnedLinearV2Label : CoefficientField m ≃+ CoefficientField m :=
  ((linearPinnedChart Q split (pinnedInput Q split c)).trans
    ((positiveRootEquiv Q split (pinnedInput Q split c) (.inl 1)).trans
      (reflectedLinearLabel Q split (pinnedInput Q split c)))).toAdditive

/-- The source right commutator with the linear root, inside the V₁ numerator. -/
def V1RightCommutator (t : CoefficientField m)
    (v : (V1Section Q split c).numerator) : (V1Section Q split c).numerator :=
  v⁻¹ * (V1Section Q split c).numeratorAction
    ((linearPinning Q split c (Theory.PSL2.SemilinearCoverage.uni t))⁻¹) v

theorem V1RightCommutator_val (t : CoefficientField m)
    (v : (V1Section Q split c).numerator) :
    (V1RightCommutator Q split c t v : X ⧸ Q.D) =
      (v : X ⧸ Q.D)⁻¹ * (linearPinnedChart Q split c (.ofAdd t) : X ⧸ Q.D)⁻¹ * v *
        linearPinnedChart Q split c (.ofAdd t) := by
  change (v : X ⧸ Q.D)⁻¹ *
    ((linearPinning Q split c (Theory.PSL2.SemilinearCoverage.uni t) : X ⧸ Q.D)⁻¹ * v *
      ((linearPinning Q split c (Theory.PSL2.SemilinearCoverage.uni t) : X ⧸ Q.D)⁻¹)⁻¹) = _
  simp only [linearPinnedChart_coe,inv_inv,mul_assoc]

/-- The pinned natural matrix reads the leading coefficient of the mixed commutator. -/
theorem V1RightCommutator_simple_coordinates (t a b : CoefficientField m) :
    V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
      (V1RightCommutator Q split c t
        (inclusion (simpleSuzuki_le_linearRemainder Q split c) (suzukiChart Q split c (a,b)))))) =
      ![t*V1BasisLabel Q split c a,0] := by
  let : Algebra (ZMod 2) (CoefficientField m) := ZMod.algebra _ 2
  let v : (V1Section Q split c).numerator :=
    inclusion (simpleSuzuki_le_linearRemainder Q split c) (suzukiChart Q split c (a,b))
  let r := linearPinning Q split c (Theory.PSL2.SemilinearCoverage.uni t)
  have hr : r⁻¹ = r := by
    apply Subtype.ext
    simpa only [Subgroup.coe_inv,linearPinnedChart_coe] using
      congrArg (fun z : simpleRoot Q split 0 => (z : X ⧸ Q.D)) (linearPinnedChart_inv Q split c t)
  let v' := (V1Section Q split c).numeratorAction r⁻¹ v
  have hq : (QuotientGroup.mk (V1RightCommutator Q split c t v) : (V1Section Q split c).Carrier) =
      (QuotientGroup.mk v)⁻¹ * QuotientGroup.mk v' := by
    exact (QuotientGroup.mk' (V1Section Q split c).denominator).map_mul v⁻¹ v' |>.trans
      (by rw [map_inv]; rfl)
  have hc : V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v)) =
      ![0,V1BasisLabel Q split c a] := V1BasisCoordinates_suzukiChart Q split c a b
  have ha := V1BasisCoordinates_source Q split c r v
  rw [show (linearPinning Q split c).symm r = Theory.PSL2.SemilinearCoverage.uni t from
    (linearPinning Q split c).symm_apply_apply _,hc] at ha
  have hv' : V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v')) =
      ![t*V1BasisLabel Q split c a,V1BasisLabel Q split c a] := by
    dsimp only [v']
    rw [hr,ha]
    rw [Representation.SL2.BinarySmall.natural_apply,Theory.PSL2.SemilinearCoverage.uni_val]
    ext i
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  rw [hq]
  change (V1BasisCoordinates Q split c).toLinearEquiv.toAddEquiv
    (-Additive.ofMul (QuotientGroup.mk v)+Additive.ofMul (QuotientGroup.mk v')) = _
  rw [map_add,map_neg]
  change -V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v))+
    V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v')) = _
  rw [hc,hv']
  ext i
  fin_cases i <;> simp

/-- Both quotients read one and the same mixed source commutator. -/
theorem fieldLabel_mixed_comparison (t a : CoefficientField m) :
    ∃ z : CoefficientField m,
      V1BasisLabel Q split (pinnedInput Q split c) z =
        t*V1BasisLabel Q split (pinnedInput Q split c) a ∧
      V2MiddleFieldLabel Q split c z = a*pinnedLinearV2Label Q split c t := by
  let d := pinnedInput Q split c
  let u := suzukiChart Q split d (a,0)
  let x := linearPinnedChart Q split d (.ofAdd t)
  let v : (V1Section Q split d).numerator :=
    inclusion (simpleSuzuki_le_linearRemainder Q split d) u
  let w : (V2Section Q split d).numerator :=
    inclusion (simpleLinear_le_suzukiRemainder Q split d) x
  let k₁ := V1RightCommutator Q split d t v
  let k₂ := V2RightCommutator Q split d u w
  have he : ((k₁⁻¹ : (V1Section Q split d).numerator) : X ⧸ Q.D) = k₂ := by
    rw [Subgroup.coe_inv,V1RightCommutator_val,V2RightCommutator_val]
    change ((u : X ⧸ Q.D)⁻¹ * (x : X ⧸ Q.D)⁻¹ * u * x)⁻¹ =
      (x : X ⧸ Q.D)⁻¹ * (u : X ⧸ Q.D)⁻¹ * x * u
    simp only [mul_inv_rev,inv_inv,mul_assoc]
  obtain ⟨z,hz₁,hz₂⟩ := V1_V2_common_parameter Q split c k₁⁻¹ k₂ he
  have hk₁ : V1BasisCoordinates Q split d (Additive.ofMul (QuotientGroup.mk k₁⁻¹)) =
      ![t*V1BasisLabel Q split d a,0] := by
    let : Algebra (ZMod 2) (CoefficientField m) := ZMod.algebra _ 2
    rw [QuotientGroup.mk_inv]
    change (V1BasisCoordinates Q split d).toLinearEquiv.toAddEquiv
      (-Additive.ofMul (QuotientGroup.mk k₁)) = _
    rw [map_neg]
    change -V1BasisCoordinates Q split d (Additive.ofMul (QuotientGroup.mk k₁)) = _
    rw [V1RightCommutator_simple_coordinates]
    ext i
    fin_cases i <;> simp [CharTwo.neg_eq]
  have hw := pinnedV2_simpleLinear Q split c x
  change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk w)) =
    ![0,0,0,pinnedLinearV2Label Q split c t] at hw
  have hk₂ := V2RightCommutator_coordinates Q split d a 0 w
  dsimp only at hk₂
  rw [hw] at hk₂
  refine ⟨z,?_,?_⟩
  · exact (congrFun hz₁ 0).symm.trans (congrFun hk₁ 0)
  · exact hz₂.symm.trans (by
      simpa only [Matrix.cons_val,Fin.isValue,Matrix.head_cons,mul_zero,mul_one,add_zero,zero_add] using congrFun hk₂ 2)


/-- The two middle V₂ lines differ from their original field parameters by one scalar. -/
theorem V2MiddleFieldLabel_scalar (a : CoefficientField m) :
    V2MiddleFieldLabel Q split c a = a*pinnedLinearV2Label Q split c 1 := by
  obtain ⟨z,hz₁,hz₂⟩ := fieldLabel_mixed_comparison Q split c 1 a
  have hz : z = a := (V1BasisLabel Q split (pinnedInput Q split c)).injective
    (by simpa only [one_mul] using hz₁)
  simpa only [hz] using hz₂

/-- The linear V₂ line and the V₁ field label are synchronized by the same scalar. -/
theorem pinnedLinearV2Label_formula (t : CoefficientField m) :
    pinnedLinearV2Label Q split c t =
      (V1BasisLabel Q split (pinnedInput Q split c)).symm t * pinnedLinearV2Label Q split c 1 := by
  obtain ⟨z,hz₁,hz₂⟩ := fieldLabel_mixed_comparison Q split c t 1
  rw [V1BasisLabel_one,mul_one] at hz₁
  have hz : z = (V1BasisLabel Q split (pinnedInput Q split c)).symm t :=
    (V1BasisLabel Q split (pinnedInput Q split c)).injective
      (hz₁.trans ((V1BasisLabel Q split (pinnedInput Q split c)).apply_symm_apply t).symm)
  rw [one_mul, V2MiddleFieldLabel_scalar,hz] at hz₂
  exact hz₂.symm

theorem pinnedLinearV2Label_one_ne_zero : pinnedLinearV2Label Q split c 1 ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : CoefficientField m) ≠ 0)
    ((pinnedLinearV2Label Q split c).injective (h.trans (map_zero _).symm))

/-- Multiplicativity is forced by the same mixed commutator in the two actual sections. -/
theorem V1BasisLabel_mul (a b : CoefficientField m) :
    V1BasisLabel Q split (pinnedInput Q split c) (a*b) =
      V1BasisLabel Q split (pinnedInput Q split c) a * V1BasisLabel Q split (pinnedInput Q split c) b := by
  obtain ⟨z,hz₁,hz₂⟩ := fieldLabel_mixed_comparison Q split c
    (V1BasisLabel Q split (pinnedInput Q split c) a) b
  have hz : z = a*b := by
    apply mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    calc
      z*pinnedLinearV2Label Q split c 1 = V2MiddleFieldLabel Q split c z :=
        (V2MiddleFieldLabel_scalar Q split c z).symm
      _ = b*pinnedLinearV2Label Q split c (V1BasisLabel Q split (pinnedInput Q split c) a) := hz₂
      _ = b*(a*pinnedLinearV2Label Q split c 1) := by
        rw [pinnedLinearV2Label_formula,AddEquiv.symm_apply_apply]
      _ = (a*b)*pinnedLinearV2Label Q split c 1 := by ring
  simpa only [hz] using hz₁

/-- The field automorphism determined by the linear natural module and common source commutators. -/
def synchronizedField : CoefficientField m ≃+* CoefficientField m :=
  { V1BasisLabel Q split (pinnedInput Q split c) with
    map_mul' := V1BasisLabel_mul Q split c }

@[simp] theorem synchronizedField_apply (a : CoefficientField m) :
    synchronizedField Q split c a = V1BasisLabel Q split (pinnedInput Q split c) a := rfl

/-- Relabeling the whole linear pinning preserves both group operations and the specified reflection. -/
def synchronizedLinearChart : Multiplicative (CoefficientField m) ≃* simpleRoot Q split 0 :=
  (synchronizedField Q split c).toAddEquiv.toMultiplicative.trans
    (linearPinnedChart Q split (pinnedInput Q split c))

/-- Its actual V₂ coordinate now uses the common source parameter times one scalar. -/
theorem synchronizedLinearChart_V2 (a : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (V2SimpleLinear Q split (pinnedInput Q split c)
        (synchronizedLinearChart Q split c (.ofAdd a)))) =
      ![0,0,0,a*pinnedLinearV2Label Q split c 1] := by
  have h := pinnedV2_simpleLinear Q split c (synchronizedLinearChart Q split c (.ofAdd a))
  change V2Coordinates Q split (pinnedInput Q split c) _ =
    ![0,0,0,pinnedLinearV2Label Q split c (V1BasisLabel Q split (pinnedInput Q split c) a)] at h
  rw [pinnedLinearV2Label_formula,AddEquiv.symm_apply_apply] at h
  exact h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
