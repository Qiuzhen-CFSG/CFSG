module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V2MiddleLines

/-!
# Literal cross commutators on the first Suzuki natural quotient

The source right commutator v⁻¹u⁻¹vu is computed through the actual inverse
Suzuki action on Uₛ₂/T₂, with the native chart correction and θ=titsEnd.
The natural basis realizes its coordinates as products of the source roots.
For v in U₂^(s₁s₂), relation (10.2)(ii) places the commutator in U₁^s₂;
injectivity of that line upgrades the coordinate calculation to an equality
in the source group, retaining the unsynchronized additive labels.

For v in U₂^s₁, the calculation gives both directions of (10.5): its
commutator factors through U₂^(s₁s₂) and U₁^s₂ modulo T₂, and each such
product is realized by one commutator. Bijectivity of θ supplies the actor
parameter in the reverse direction, also at q = 2.

Source: Fong--Seitz II (1974), (10.5), p.222, and (10.7)--(10.8), p.223.
The linear section and the subsequent comparison of field twists remain
separate obligations. OriginalV2Middle applies the exact identity to the
original positive-root representatives.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped IsMulCommutative commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- The actual right commutator v⁻¹u⁻¹vu inside the first Suzuki numerator.
The product uses the source inverse actor; it is not a Weyl-class action. -/
def V2RightCommutator (u : simpleRoot Q split 1)
    (v : (V2Section Q split c).numerator) : (V2Section Q split c).numerator :=
  v⁻¹ * (V2Section Q split c).numeratorAction (inclusion (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left) u⁻¹) v

theorem V2RightCommutator_val (u : simpleRoot Q split 1)
    (v : (V2Section Q split c).numerator) :
    (V2RightCommutator Q split c u v : X ⧸ Q.D) =
      (v : X ⧸ Q.D)⁻¹ * (u : X ⧸ Q.D)⁻¹ * v * u := by
  change (v : X ⧸ Q.D)⁻¹ * ((u : X ⧸ Q.D)⁻¹ * v * ((u : X ⧸ Q.D)⁻¹)⁻¹) = _
  group

/-- Right commutator coordinates on the literal first Suzuki layer, in the
corrected root chart. The cubic coefficient is unchanged on inversion. -/
theorem V2RightCommutator_coordinates (a b : CoefficientField m)
    (v : (V2Section Q split c).numerator) :
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
      (V2RightCommutator Q split c (suzukiChart Q split c (a,b)) v))) =
      let x := V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))
      ![a*x 1+b*x 2+(a^2*titsEnd m a+a*b+titsEnd m b)*x 3,
        titsEnd m a*x 2+(b+a*titsEnd m a)*x 3,a*x 3,0] := by
  let x := V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))
  let r := (V2Section Q split c).numeratorAction
    (inclusion (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left) (suzukiChart Q split c (a,b))⁻¹) v
  have hr : r = (V2Section Q split c).numeratorAction
      (inclusion (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left) (suzukiChart Q split c (a,b+a*titsEnd m a))) v := by
    dsimp only [r]
    rw [suzukiChart_inverse]
  have hq : (QuotientGroup.mk (V2RightCommutator Q split c (suzukiChart Q split c (a,b)) v) :
      (V2Section Q split c).Carrier) =
      (QuotientGroup.mk v)⁻¹ * QuotientGroup.mk r := by
    exact (QuotientGroup.mk' (V2Section Q split c).denominator).map_mul v⁻¹ r |>.trans
      (by rw [map_inv]; rfl)
  have h := congrArg (fun w : (V2Section Q split c).Carrier =>
    V2Coordinates Q split c (Additive.ofMul w)) hq
  change _ = (V2Coordinates Q split c).toLinearEquiv
    (-Additive.ofMul (QuotientGroup.mk v) + Additive.ofMul (QuotientGroup.mk r)) at h
  rw [map_add,map_neg] at h
  apply h.trans
  have he := congrArg (fun w : (V2Section Q split c).numerator =>
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk w))) hr
  have he := he.trans (V2Coordinates_suzukiChart Q split c a (b+a*titsEnd m a) v)
  change -x + V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk r)) = _
  rw [he]
  change -x + ![x 0+a*x 1+(b+a*titsEnd m a+a*titsEnd m a)*x 2+
      (a^2*titsEnd m a+a*(b+a*titsEnd m a)+titsEnd m (b+a*titsEnd m a))*x 3,
      x 1+titsEnd m a*x 2+(b+a*titsEnd m a)*x 3,x 2+a*x 3,x 3] = _
  simp only [map_add,map_mul,titsEnd_twice]
  ext i
  fin_cases i
  · dsimp
    linear_combination (norm := ring_nf)
      (a*x 2+a^2*x 3) * CharTwo.add_self_eq_zero (titsEnd m a)
    dsimp only [x]
    ring
  · dsimp; ring
  · dsimp; ring
  · dsimp; ring

/-- A four-root product for every right commutator in the first natural
section. Each coordinate is realized by the literal roots in the (10.4) basis. -/
theorem V2RightCommutator_naturalPoint
    (σ : CoefficientField m ≃+* CoefficientField m) (a b : CoefficientField m)
    (v : (V2Section Q split (pinnedInput Q split c)).numerator) :
    QuotientGroup.mk (V2RightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b)) v) =
      let x := V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v))
      V2NaturalPoint Q split c σ
        ![a*x 1+b*x 2+(a^2*titsEnd m a+a*b+titsEnd m b)*x 3,
          titsEnd m a*x 2+(b+a*titsEnd m a)*x 3,a*x 3,0] := by
  apply (V2Coordinates Q split (pinnedInput Q split c)).injective
  exact (V2RightCommutator_coordinates Q split (pinnedInput Q split c) a b v).trans
    (V2NaturalPoint_coordinates Q split c σ _).symm

/-- The literal mixed commutator (10.8), before the independent field labels
are synchronized. This equality holds in the source group itself. -/
theorem pinned_shiftedSuzuki_right_commutator
    (σ : CoefficientField m ≃+* CoefficientField m) (a b y z : CoefficientField m) :
    (positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (y,z))⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (y,z) *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) =
      positivePoint Q split (pinnedInput Q split c) σ (.inl 1)
        ((reflectedLinearFieldLabel Q split (pinnedInput Q split c) σ).symm
          (a*V2MiddleFieldLabel Q split c y)) := by
  let d := pinnedInput Q split c
  let u := suzukiChart Q split d (a,b)
  let v : (V2Section Q split d).numerator :=
    inclusion (positiveRoot_le_remainder Q split d (.inr 3) 1 (by decide))
      (positiveChart Q split d (RingEquiv.refl _) (.inr 3) (y,z))
  let k := V2RightCommutator Q split d u v
  have hk : (k : X ⧸ Q.D) ∈ positiveRoot Q split (.inl 1) := by
    have he : ⁅positiveRoot Q split (.inr 3),simpleRoot Q split 1⁆ = positiveRoot Q split (.inl 1) := by
      rw [commutator_comm]
      simpa only [nConj,U,Uat,OneMemClass.coe_one,rightConjugate_one,
        positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons]
        using d.relations.ten_two_ii_left 1
    apply he.le
    have hh := commutator_mem_commutator
      ((positiveRoot Q split (.inr 3)).inv_mem
        (positiveChart Q split d (RingEquiv.refl _) (.inr 3) (y,z)).property)
      ((simpleRoot Q split 1).inv_mem u.property)
    change ⁅(v : X ⧸ Q.D)⁻¹,(u : X ⧸ Q.D)⁻¹⁆ ∈
      ⁅positiveRoot Q split (.inr 3),simpleRoot Q split 1⁆ at hh
    simpa only [k,V2RightCommutator_val,commutatorElement_def,inv_inv] using hh
  let k' : positiveRoot Q split (.inl 1) := ⟨k,hk⟩
  have hk' : reflectedLinearCoordinate Q split d k' = a*V2MiddleFieldLabel Q split c y := by
    have hh := V2RightCommutator_coordinates Q split d a b v
    change V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d k')) = _ at hh
    have hv := pinnedV2_shifted_parameter Q split c y z
    change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk v)) = _ at hv
    dsimp only at hh
    rw [hv,V2Coordinates_reflectedLinear] at hh
    change V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d k')) 0 =
      a*V2MiddleLabelHom Q split c y
    simpa using congrFun hh 0
  have he : k' = positiveChart Q split d σ (.inl 1)
      ((reflectedLinearFieldLabel Q split d σ).symm (a*V2MiddleFieldLabel Q split c y)) := by
    apply reflectedLinearCoordinate_injective Q split d
    change reflectedLinearCoordinate Q split d k' = reflectedLinearFieldLabel Q split d σ
      ((reflectedLinearFieldLabel Q split d σ).symm (a*V2MiddleFieldLabel Q split c y))
    rw [AddEquiv.apply_symm_apply]
    exact hk'
  exact (V2RightCommutator_val Q split d u v).symm.trans (congrArg Subtype.val he)

/-- The opposite Suzuki cross commutator is exactly a product of the two
first natural root lines modulo the literal T₂. This is the containment
in (10.5), with both unsynchronized labels still visible. -/
theorem V2_cross_commutator_factorization
    (σ : CoefficientField m ≃+* CoefficientField m) (a b y z : CoefficientField m) :
    QuotientGroup.mk (V2RightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b))
      (inclusion (positiveRoot_le_remainder Q split (pinnedInput Q split c) (.inr 2) 1 (by decide))
        (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 2) (y,z)))) =
    V2ShiftedSuzuki Q split (pinnedInput Q split c)
      (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3)
        ((V2MiddleFieldLabel Q split c).symm (titsEnd m a*V2MiddleFieldLabel Q split c y),0)) *
    V2ReflectedLinear Q split (pinnedInput Q split c)
      (positiveChart Q split (pinnedInput Q split c) σ (.inl 1)
        ((reflectedLinearFieldLabel Q split (pinnedInput Q split c) σ).symm
          (b*V2MiddleFieldLabel Q split c y))) := by
  let d := pinnedInput Q split c
  let τ := V2MiddleFieldLabel Q split c
  let ℓ := reflectedLinearFieldLabel Q split d σ
  let v : (V2Section Q split d).numerator :=
    inclusion (positiveRoot_le_remainder Q split d (.inr 2) 1 (by decide))
      (positiveChart Q split d (RingEquiv.refl _) (.inr 2) (y,z))
  let v₁ := V2ShiftedSuzuki Q split d
    (positiveChart Q split d (RingEquiv.refl _) (.inr 3) (τ.symm (titsEnd m a*τ y),0))
  let v₀ := V2ReflectedLinear Q split d
    (positiveChart Q split d σ (.inl 1) (ℓ.symm (b*τ y)))
  have hv : V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk v)) = ![0,0,τ y,0] :=
    pinnedV2_opposite_parameter Q split c y z
  have hc : V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk
      (V2RightCommutator Q split d (suzukiChart Q split d (a,b)) v))) =
      ![b*τ y,titsEnd m a*τ y,0,0] := by
    have h := V2RightCommutator_coordinates Q split d a b v
    dsimp only at h
    rw [hv] at h
    simpa only [Matrix.cons_val,Fin.isValue,Matrix.head_cons,mul_zero,zero_add,add_zero] using h
  have h₁ : V2Coordinates Q split d (Additive.ofMul v₁) = ![0,titsEnd m a*τ y,0,0] := by
    exact (pinnedV2_shifted_parameter Q split c _ _).trans
      (by change ![0,τ (τ.symm _),0,0] = _; rw [AddEquiv.apply_symm_apply])
  have h₀ : V2Coordinates Q split d (Additive.ofMul v₀) = ![b*τ y,0,0,0] := by
    exact (V2Coordinates_reflectedLinear Q split d _).trans
      (by change ![ℓ (ℓ.symm _),0,0,0] = _; rw [AddEquiv.apply_symm_apply])
  apply (V2Coordinates Q split d).injective
  change V2Coordinates Q split d (Additive.ofMul (QuotientGroup.mk
    (V2RightCommutator Q split d (suzukiChart Q split d (a,b)) v))) =
    (V2Coordinates Q split d).toLinearEquiv (Additive.ofMul v₁+Additive.ofMul v₀)
  rw [map_add]
  change _ = V2Coordinates Q split d (Additive.ofMul v₁)+V2Coordinates Q split d (Additive.ofMul v₀)
  rw [hc,h₁,h₀]
  ext i
  fin_cases i <;> simp

/-- Every product in the right side of (10.5) is already one actual cross
commutator modulo T₂. Thus the previous containment is an equality, including q=2. -/
theorem V2_cross_commutator_covers
    (σ : CoefficientField m ≃+* CoefficientField m) (p q : CoefficientField m) :
    ∃ a b y : CoefficientField m,
      QuotientGroup.mk (V2RightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (inclusion (positiveRoot_le_remainder Q split (pinnedInput Q split c) (.inr 2) 1 (by decide))
          (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 2) (y,0)))) =
      V2ShiftedSuzuki Q split (pinnedInput Q split c)
        (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (p,0)) *
      V2ReflectedLinear Q split (pinnedInput Q split c)
        (positiveChart Q split (pinnedInput Q split c) σ (.inl 1) q) := by
  let τ := V2MiddleFieldLabel Q split c
  let ℓ := reflectedLinearFieldLabel Q split (pinnedInput Q split c) σ
  let a := (titsAutomorphism m).symm (τ p)
  have ha : titsEnd m a = τ p := (titsAutomorphism m).apply_symm_apply _
  refine ⟨a,ℓ q,τ.symm 1,?_⟩
  have h := V2_cross_commutator_factorization Q split c σ a (ℓ q) (τ.symm 1) 0
  change _ = V2ShiftedSuzuki Q split (pinnedInput Q split c)
    (positiveChart Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3)
      (τ.symm (titsEnd m a*τ (τ.symm 1)),0)) *
    V2ReflectedLinear Q split (pinnedInput Q split c)
      (positiveChart Q split (pinnedInput Q split c) σ (.inl 1)
        (ℓ.symm (ℓ q*τ (τ.symm 1)))) at h
  rw [AddEquiv.apply_symm_apply,ha,mul_one,mul_one,
    AddEquiv.symm_apply_apply,AddEquiv.symm_apply_apply] at h
  exact h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
