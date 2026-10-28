module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SynchronizedTorus

/-!
# The Suzuki row and reflected linear entry of the synchronized torus table

The natural V₂ action determines the four nonperpendicular root weights.
Pure-scalar Cartan action on whole Suzuki roots then determines their central
weights as well; the perpendicular root is centralized by the whole Suzuki
rank-one actor. This proves the complete Suzuki row of (10.10), including
whole-root second coordinates and q=2. The linear reflection inverts its
own torus and yields the opposite Suzuki weights in (10.12).

All conjugations use the same supplied reflections and literal source quotient.
Source: Fong–Seitz II (1974), printed pp.223–224, (10.10) and (10.12).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4 BenderSuzuki.MatrixGroups
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

theorem synchronizedLinearTorus_reflection (a : (CoefficientField m)ˣ) :
    ((c.reflections 0).val : X ⧸ Q.D)*synchronizedLinearTorus Q split c a*
      ((c.reflections 0).val : X ⧸ Q.D)⁻¹ = synchronizedLinearTorus Q split c a⁻¹ := by
  have h := GTwoSource.reflection_alignedTorus Q split 0
    (linearRemainder_le_kernel Q split (pinnedInput Q split c))
    (linearLocalMarking Q split (pinnedInput Q split c)) (c.reflections 0)
      (Units.map (synchronizedField Q split c).toMonoidHom a)
  simp only [synchronizedLinearTorus,MonoidHom.comp_apply,GTwoSource.alignedTorusHom_apply]
  rw [map_inv]
  exact h

theorem synchronizedLinearTorus_oppositeSuzuki (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 2) (x,y) *
        synchronizedLinearTorus Q split c a =
      synchronizedPositivePoint Q split c (.inr 2)
        ((a : CoefficientField m)⁻¹*x,
          (a : CoefficientField m)⁻¹*(titsEnd m a)⁻¹*y) := by
  let s : X ⧸ Q.D := (c.reflections 0).val
  let h := synchronizedLinearTorus Q split c a
  have hh : s*h*s⁻¹ = h⁻¹ := by
    simpa only [map_inv] using synchronizedLinearTorus_reflection Q split c a
  have hi : s*h⁻¹*s⁻¹ = h := by
    calc
      s*h⁻¹*s⁻¹ = (s*h*s⁻¹)⁻¹ := (map_inv (MulAut.conj s) h)
      _ = h := by rw [hh,inv_inv]
  have hc := synchronizedLinearTorus_suzuki Q split c a⁻¹ x y
  rw [map_inv,inv_inv,Units.val_inv_eq_inv_val,map_inv₀] at hc
  change h⁻¹*(s⁻¹*(suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D)*s)*h =
    s⁻¹*(suzukiChart Q split (pinnedInput Q split c)
      ((a : CoefficientField m)⁻¹*x,(a : CoefficientField m)⁻¹*(titsEnd m a)⁻¹*y) : X ⧸ Q.D)*s
  calc
    _ = s⁻¹*((s*h⁻¹*s⁻¹)*(suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D)*
      (s*h*s⁻¹))*s := by group
    _ = _ := by rw [hi,hh,hc]

private theorem suzukiTorus_inverse (a : (CoefficientField m)ˣ) :
    (synchronizedSuzukiTorus Q split c a)⁻¹ =
      (pinnedSuzukiTorus Q split c (matrixTorusParameter a) : X ⧸ Q.D) := by
  rw [←map_inv,synchronizedSuzukiTorus_apply,inv_inv]

theorem synchronizedSuzukiTorus_shifted (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 3) (x,y) *
        synchronizedSuzukiTorus Q split c a =
      synchronizedPositivePoint Q split c (.inr 3)
        ((a : CoefficientField m)^(2^m)*x,
          (a : CoefficientField m)^(2^m)*titsEnd m ((a : CoefficientField m)^(2^m))*y) := by
  let d := pinnedInput Q split c
  let r := pinnedSuzukiTorus Q split c (matrixTorusParameter a)
  let h : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨r,pinnedSuzukiTorus_mem_cartan Q split c _⟩
  obtain ⟨b,hb⟩ := cartan_positiveSuzuki_scalar Q split c h 3
  let v : (V2Section Q split d).numerator :=
    inclusion (positiveRoot_le_remainder Q split d (.inr 3) 1 (by decide))
      (synchronizedPositiveChart Q split c (.inr 3) (1,0))
  have hv : (V2Section Q split d).numeratorAction r v =
      inclusion (positiveRoot_le_remainder Q split d (.inr 3) 1 (by decide))
        (synchronizedPositiveChart Q split c (.inr 3) ((b : CoefficientField m),0)) := by
    apply Subtype.ext
    change (h : X ⧸ Q.D)*synchronizedPositivePoint Q split c (.inr 3) (1,0)*
      (h : X ⧸ Q.D)⁻¹ = synchronizedPositivePoint Q split c (.inr 3) ((b : CoefficientField m),0)
    simpa only [mul_one,mul_zero] using hb 1 0
  have hc := synchronizedSuzukiTorus_V2 Q split c a v
  rw [hv] at hc
  change V2Coordinates Q split d (Additive.ofMul (V2ShiftedSuzuki Q split d
      (synchronizedPositiveChart Q split c (.inr 3) ((b : CoefficientField m),0)))) =
    let z := V2Coordinates Q split d (Additive.ofMul (V2ShiftedSuzuki Q split d
      (synchronizedPositiveChart Q split c (.inr 3) (1,0))))
    ![(a : CoefficientField m)^(1+2^m)*z 0,
      (a : CoefficientField m)^(2^m)*z 1,
      ((a : CoefficientField m)^(2^m))⁻¹*z 2,
      ((a : CoefficientField m)^(1+2^m))⁻¹*z 3] at hc
  rw [synchronized_shifted_coordinates,synchronized_shifted_coordinates] at hc
  have hbval : (b : CoefficientField m) = (a : CoefficientField m)^(2^m) := by
    apply mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,one_mul] using congrFun hc 1
  have he := hb x y
  rw [hbval] at he
  rw [suzukiTorus_inverse]
  change (r : X ⧸ Q.D)*synchronizedPositivePoint Q split c (.inr 3) (x,y)*_ = _
  rw [show synchronizedSuzukiTorus Q split c a = (r : X ⧸ Q.D)⁻¹ from
    by simpa only [inv_inv] using congrArg Inv.inv (suzukiTorus_inverse Q split c a)]
  exact he

theorem synchronizedSuzukiTorus_opposite (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 2) (x,y) *
        synchronizedSuzukiTorus Q split c a =
      synchronizedPositivePoint Q split c (.inr 2)
        (((a : CoefficientField m)^(2^m))⁻¹*x,
          ((a : CoefficientField m)^(2^m))⁻¹*titsEnd m (((a : CoefficientField m)^(2^m))⁻¹)*y) := by
  let d := pinnedInput Q split c
  let r := pinnedSuzukiTorus Q split c (matrixTorusParameter a)
  let h : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨r,pinnedSuzukiTorus_mem_cartan Q split c _⟩
  obtain ⟨b,hb⟩ := cartan_positiveSuzuki_scalar Q split c h 2
  let v : (V2Section Q split d).numerator :=
    inclusion (positiveRoot_le_remainder Q split d (.inr 2) 1 (by decide))
      (synchronizedPositiveChart Q split c (.inr 2) (1,0))
  have hv : (V2Section Q split d).numeratorAction r v =
      inclusion (positiveRoot_le_remainder Q split d (.inr 2) 1 (by decide))
        (synchronizedPositiveChart Q split c (.inr 2) ((b : CoefficientField m),0)) := by
    apply Subtype.ext
    change (h : X ⧸ Q.D)*synchronizedPositivePoint Q split c (.inr 2) (1,0)*
      (h : X ⧸ Q.D)⁻¹ = synchronizedPositivePoint Q split c (.inr 2) ((b : CoefficientField m),0)
    simpa only [mul_one,mul_zero] using hb 1 0
  have hc := synchronizedSuzukiTorus_V2 Q split c a v
  rw [hv] at hc
  change V2Coordinates Q split d (Additive.ofMul (V2OppositeSuzuki Q split d
      (synchronizedPositiveChart Q split c (.inr 2) ((b : CoefficientField m),0)))) =
    let z := V2Coordinates Q split d (Additive.ofMul (V2OppositeSuzuki Q split d
      (synchronizedPositiveChart Q split c (.inr 2) (1,0))))
    ![(a : CoefficientField m)^(1+2^m)*z 0,
      (a : CoefficientField m)^(2^m)*z 1,
      ((a : CoefficientField m)^(2^m))⁻¹*z 2,
      ((a : CoefficientField m)^(1+2^m))⁻¹*z 3] at hc
  rw [synchronized_opposite_coordinates,synchronized_opposite_coordinates] at hc
  have hbval : (b : CoefficientField m) = ((a : CoefficientField m)^(2^m))⁻¹ := by
    apply mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    simpa only [Matrix.cons_val,Fin.isValue,Matrix.head_cons,one_mul] using congrFun hc 2
  have he := hb x y
  rw [hbval] at he
  rw [suzukiTorus_inverse]
  change (r : X ⧸ Q.D)*synchronizedPositivePoint Q split c (.inr 2) (x,y)*_ = _
  rw [show synchronizedSuzukiTorus Q split c a = (r : X ⧸ Q.D)⁻¹ from
    by simpa only [inv_inv] using congrArg Inv.inv (suzukiTorus_inverse Q split c a)]
  exact he

theorem synchronizedSuzukiTorus_perpendicular (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 1) (x,y) *
        synchronizedSuzukiTorus Q split c a =
      synchronizedPositivePoint Q split c (.inr 1) (x,y) := by
  have hc := pinnedSuzukiTorus_centralizes_perpendicular Q split c (matrixTorusParameter a⁻¹)
  have hh := mem_centralizer_iff.mp hc _
    (synchronizedPositiveChart Q split c (.inr 1) (x,y)).property
  change synchronizedPositivePoint Q split c (.inr 1) (x,y)*
    synchronizedSuzukiTorus Q split c a =
      synchronizedSuzukiTorus Q split c a*synchronizedPositivePoint Q split c (.inr 1) (x,y) at hh
  rw [mul_assoc,hh,inv_mul_cancel_left]

private theorem V2SimpleLinear_pinned_injective :
    Function.Injective (V2SimpleLinear Q split (pinnedInput Q split c)) := by
  intro u v huv
  obtain ⟨x,rfl⟩ := (synchronizedLinearChart Q split c).surjective u
  obtain ⟨y,rfl⟩ := (synchronizedLinearChart Q split c).surjective v
  have he := congrArg (fun z => V2Coordinates Q split (pinnedInput Q split c)
    (Additive.ofMul z)) huv
  change V2Coordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (V2SimpleLinear Q split (pinnedInput Q split c)
      (synchronizedLinearChart Q split c (.ofAdd x.toAdd)))) =
    V2Coordinates Q split (pinnedInput Q split c)
    (Additive.ofMul (V2SimpleLinear Q split (pinnedInput Q split c)
      (synchronizedLinearChart Q split c (.ofAdd y.toAdd)))) at he
  rw [synchronizedLinearChart_V2,synchronizedLinearChart_V2] at he
  have hxy : x.toAdd = y.toAdd := mul_right_cancel₀
    (pinnedLinearV2Label_one_ne_zero Q split c) (congrFun he 3)
  exact congrArg (synchronizedLinearChart Q split c)
    (Multiplicative.toAdd.injective hxy)

theorem synchronizedSuzukiTorus_linear (a : (CoefficientField m)ˣ) (x : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c a)⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D) *
        synchronizedSuzukiTorus Q split c a =
      synchronizedLinearChart Q split c
        (.ofAdd (((a : CoefficientField m)^(1+2^m))⁻¹*x)) := by
  let d := pinnedInput Q split c
  let r := pinnedSuzukiTorus Q split c (matrixTorusParameter a)
  let z : simpleRoot Q split 0 := (simpleRoot Q split 0).normalizerMonoidHom
    ⟨r,torus_normalizes_simpleRoot Q split 0 (pinnedSuzukiTorus_mem_cartan Q split c _)⟩
      (synchronizedLinearChart Q split c (.ofAdd x))
  have he : z = synchronizedLinearChart Q split c
      (.ofAdd (((a : CoefficientField m)^(1+2^m))⁻¹*x)) := by
    apply V2SimpleLinear_pinned_injective Q split c
    apply (V2Coordinates Q split d).injective
    let v : (V2Section Q split d).numerator :=
      inclusion (simpleLinear_le_suzukiRemainder Q split d)
        (synchronizedLinearChart Q split c (.ofAdd x))
    have hv : (V2Section Q split d).numeratorAction r v =
        inclusion (simpleLinear_le_suzukiRemainder Q split d) z := Subtype.ext rfl
    have hc := synchronizedSuzukiTorus_V2 Q split c a v
    rw [hv] at hc
    change V2Coordinates Q split d (Additive.ofMul (V2SimpleLinear Q split d z)) =
      V2Coordinates Q split d (Additive.ofMul (V2SimpleLinear Q split d
        (synchronizedLinearChart Q split c
          (.ofAdd (((a : CoefficientField m)^(1+2^m))⁻¹*x)))))
    rw [synchronizedLinearChart_V2]
    refine hc.trans ?_
    change (let p := V2Coordinates Q split d (Additive.ofMul (V2SimpleLinear Q split d
      (synchronizedLinearChart Q split c (.ofAdd x))))
      ![(a : CoefficientField m)^(1+2^m)*p 0,(a : CoefficientField m)^(2^m)*p 1,
        ((a : CoefficientField m)^(2^m))⁻¹*p 2,((a : CoefficientField m)^(1+2^m))⁻¹*p 3]) = _
    rw [synchronizedLinearChart_V2]
    ext i
    fin_cases i <;> simp [mul_assoc]
  have he := congrArg Subtype.val he
  rw [suzukiTorus_inverse,
    show synchronizedSuzukiTorus Q split c a = (r : X ⧸ Q.D)⁻¹ from
      by simpa only [inv_inv] using congrArg Inv.inv (suzukiTorus_inverse Q split c a)]
  exact he

theorem synchronizedSuzukiTorus_reflectedLinear (a : (CoefficientField m)ˣ)
    (x : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 1) x *
        synchronizedSuzukiTorus Q split c a =
      synchronizedPositivePoint Q split c (.inl 1) ((a : CoefficientField m)^(1+2^m)*x) := by
  let d := pinnedInput Q split c
  let r := pinnedSuzukiTorus Q split c (matrixTorusParameter a)
  let z : positiveRoot Q split (.inl 1) := (positiveRoot Q split (.inl 1)).normalizerMonoidHom
    ⟨r,rootAt_torus_normalizes Q split 0 (Q.simple 1) (pinnedSuzukiTorus_mem_cartan Q split c _)⟩
      (synchronizedPositiveChart Q split c (.inl 1) x)
  have he : z = synchronizedPositiveChart Q split c (.inl 1)
      ((a : CoefficientField m)^(1+2^m)*x) := by
    apply V2ReflectedLinear_injective Q split d
    apply (V2Coordinates Q split d).injective
    let v : (V2Section Q split d).numerator :=
      inclusion (reflectedLinear_le_suzukiRemainder Q split d)
        (synchronizedPositiveChart Q split c (.inl 1) x)
    have hv : (V2Section Q split d).numeratorAction r v =
        inclusion (reflectedLinear_le_suzukiRemainder Q split d) z := Subtype.ext rfl
    have hc := synchronizedSuzukiTorus_V2 Q split c a v
    rw [hv] at hc
    change V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d z)) =
      V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d
        (synchronizedPositiveChart Q split c (.inl 1) ((a : CoefficientField m)^(1+2^m)*x))))
    rw [synchronized_reflected_coordinates]
    refine hc.trans ?_
    change (let p := V2Coordinates Q split d (Additive.ofMul (V2ReflectedLinear Q split d
      (synchronizedPositiveChart Q split c (.inl 1) x)))
      ![(a : CoefficientField m)^(1+2^m)*p 0,(a : CoefficientField m)^(2^m)*p 1,
        ((a : CoefficientField m)^(2^m))⁻¹*p 2,((a : CoefficientField m)^(1+2^m))⁻¹*p 3]) = _
    rw [synchronized_reflected_coordinates]
    ext i
    fin_cases i <;> simp [mul_assoc]
  have he := congrArg Subtype.val he
  rw [suzukiTorus_inverse,
    show synchronizedSuzukiTorus Q split c a = (r : X ⧸ Q.D)⁻¹ from
      by simpa only [inv_inv] using congrArg Inv.inv (suzukiTorus_inverse Q split c a)]
  exact he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
