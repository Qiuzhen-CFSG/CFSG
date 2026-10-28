module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiTorusTable

/-!
# Complete synchronized Ree torus table and Cartan coordinates

The two torus actors have the same action on the whole simple Suzuki root.
Their quotient therefore centralizes its rank-one group, giving the first
cross-Weyl identity. Matching their simple linear weights gives the other
identity. Conjugating through these identities proves the remaining entries
of (10.10) and the whole-root actions, hence the center entries of (10.12).

The fourth linear root detects the Suzuki factor of the product, and the
simple Suzuki root detects the linear factor. This proves injectivity of the
product map; the original Cartan order then proves its range is all of H.
All maps retain the given quotient and reflections, including the binary case.

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

theorem synchronizedTorus_quotient_centralizes_suzuki (a : (CoefficientField m)ˣ) :
    synchronizedLinearTorus Q split c a * (synchronizedSuzukiTorus Q split c a)⁻¹ ∈
      centralizer (rankOne Q split 1 : Set (X ⧸ Q.D)) := by
  let h := synchronizedLinearTorus Q split c a
  let k := synchronizedSuzukiTorus Q split c a
  have hH : h*k⁻¹ ∈ Q.tits.B ⊓ Q.tits.N :=
    (Q.tits.B ⊓ Q.tits.N).mul_mem (synchronizedLinearTorus_mem_cartan Q split c a)
      ((Q.tits.B ⊓ Q.tits.N).inv_mem (synchronizedSuzukiTorus_mem_cartan Q split c a))
  have hC : h*k⁻¹ ∈ centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro u hu
    obtain ⟨⟨x,y⟩,he⟩ := (suzukiChart Q split (pinnedInput Q split c)).surjective ⟨u,hu⟩
    have hu' : (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) = u := congrArg Subtype.val he
    have hw : h⁻¹*u*h = k⁻¹*u*k := by
      rw [←hu',synchronizedLinearTorus_suzuki,synchronizedSuzukiTorus_simple]
    have hw' := congrArg (fun z : X ⧸ Q.D => h*z*k⁻¹) hw
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_inv_cancel,mul_one] using hw'
  have hh : h*k⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N) ⊓
      centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) := ⟨hH,hC⟩
  rw [cartan_centralizer_simpleRoot,←cartan_centralizer_rankOneRootGroup Q split 1] at hh
  exact hh.2

/-- The supplied Suzuki reflection inverts its literal pinned torus. -/
theorem synchronizedSuzukiTorus_reflection (a : (CoefficientField m)ˣ) :
    ((c.reflections 1).val : X ⧸ Q.D)*synchronizedSuzukiTorus Q split c a*
      ((c.reflections 1).val : X ⧸ Q.D)⁻¹ = (synchronizedSuzukiTorus Q split c a)⁻¹ := by
  let e := suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel
  let s : rankOne Q split 1 := ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
  let r := pinnedSuzukiTorus Q split c (matrixTorusParameter a⁻¹)
  have he : s*r*s⁻¹ = r⁻¹ := by
    apply e.injective
    rw [map_mul,map_mul,map_inv,map_inv]
    have hs : e s = suzukiWeyl m := pinnedInput_reflection Q split c
    have hr : e r = (matrixTorusParameter a⁻¹ : SuzukiMatrixGroup m) :=
      pinnedSuzukiTorus_model Q split c _
    rw [hs,hr,inv_eq_of_mul_eq_one_right (suzukiWeyl_sq m),suzukiWeyl_conj_splitTorus]
  exact congrArg Subtype.val he

/-- Cross-Weyl action on the first Cartan factor, obtained inside the source
from its actual kernel on R₂. -/
theorem synchronizedLinearTorus_suzukiReflection (a : (CoefficientField m)ˣ) :
    ((c.reflections 1).val : X ⧸ Q.D)*synchronizedLinearTorus Q split c a*
      ((c.reflections 1).val : X ⧸ Q.D)⁻¹ =
      synchronizedLinearTorus Q split c a * synchronizedSuzukiTorus Q split c (a⁻¹*a⁻¹) := by
  let s : X ⧸ Q.D := (c.reflections 1).val
  let h := synchronizedLinearTorus Q split c a
  let k := synchronizedSuzukiTorus Q split c a
  have hc : s*(h*k⁻¹) = (h*k⁻¹)*s :=
    mem_centralizer_iff.mp (synchronizedTorus_quotient_centralizes_suzuki Q split c a)
      _ (c.reflections 1).mem_rankOne
  have hh : s*(h*k⁻¹)*s⁻¹ = h*k⁻¹ := by rw [hc,mul_inv_cancel_right]
  have hk : s*k*s⁻¹ = k⁻¹ := synchronizedSuzukiTorus_reflection Q split c a
  change s*h*s⁻¹ = h*synchronizedSuzukiTorus Q split c (a⁻¹*a⁻¹)
  rw [map_mul,map_inv]
  calc
    s*h*s⁻¹ = (s*(h*k⁻¹)*s⁻¹)*(s*k*s⁻¹) := by group
    _ = h*k⁻¹*k⁻¹ := by rw [hh,hk]
    _ = _ := mul_assoc _ _ _

private theorem pinnedInput_reflections (i : Fin 2) :
    (pinnedInput Q split c).reflections i = c.reflections i := rfl

private theorem synchronizedPositivePoint_linear (j : Fin 4) (x : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inl j) x =
      (positiveLift Q split (pinnedInput Q split c) (.inl j) : X ⧸ Q.D)⁻¹ *
        (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D) *
          positiveLift Q split (pinnedInput Q split c) (.inl j) := rfl

private theorem synchronizedPositivePoint_suzuki (j : Fin 4) (x y : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr j) (x,y) =
      (positiveLift Q split (pinnedInput Q split c) (.inr j) : X ⧸ Q.D)⁻¹ *
        (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) *
          positiveLift Q split (pinnedInput Q split c) (.inr j) := rfl

private theorem conjugate_right_transport {Y : Type*} [Group Y] (s h k u v : Y)
    (hs : s*h*s⁻¹ = k) (hu : k⁻¹*u*k = v) :
    h⁻¹*(s⁻¹*u*s)*h = s⁻¹*v*s := by
  calc
    h⁻¹*(s⁻¹*u*s)*h = s⁻¹*((s*h*s⁻¹)⁻¹*u*(s*h*s⁻¹))*s := by group
    _ = _ := by rw [hs,hu]

private theorem conjugate_right_product {Y : Type*} [Group Y] (h k u v w : Y)
    (hh : h⁻¹*u*h = v) (hk : k⁻¹*v*k = w) : (h*k)⁻¹*u*(h*k) = w := by
  calc
    (h*k)⁻¹*u*(h*k) = k⁻¹*(h⁻¹*u*h)*k := by group
    _ = w := by rw [hh,hk]

private theorem linear_reflected_weight (a : (CoefficientField m)ˣ) :
    (((↑(a⁻¹*a⁻¹) : CoefficientField m)^(1+2^m))⁻¹)*(a : CoefficientField m)⁻¹^2 =
      titsEnd m a := by
  rw [titsEnd_apply,pow_succ]
  simp only [Units.val_mul,Units.val_inv_eq_inv_val,mul_pow,inv_pow,mul_inv_rev,inv_inv]
  rw [pow_add,pow_one]
  field_simp
  ring

/-- The exceptional h₁ entry on U₁^s₂ in (10.10), from the actual cross-Weyl action. -/
theorem synchronizedLinearTorus_reflectedLinear (a : (CoefficientField m)ˣ)
    (x : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 1) x *
        synchronizedLinearTorus Q split c a =
      synchronizedPositivePoint Q split c (.inl 1) (titsEnd m a*x) := by
  have hh := conjugate_right_product
    (synchronizedLinearTorus Q split c a)
    (synchronizedSuzukiTorus Q split c (a⁻¹*a⁻¹))
    (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D)
    (synchronizedLinearChart Q split c (.ofAdd ((a : CoefficientField m)⁻¹^2*x)) : X ⧸ Q.D)
    (synchronizedLinearChart Q split c (.ofAdd (titsEnd m a*x)) : X ⧸ Q.D)
    (synchronizedLinearTorus_simple Q split c a x) (by
      rw [synchronizedSuzukiTorus_linear,←mul_assoc,linear_reflected_weight])
  exact conjugate_right_transport ((c.reflections 1).val : X ⧸ Q.D)
    (synchronizedLinearTorus Q split c a) _ _ _
    (synchronizedLinearTorus_suzukiReflection Q split c a) hh

private theorem linear_shifted_weight (a : (CoefficientField m)ˣ) :
    (((↑(a⁻¹*a⁻¹) : CoefficientField m)^(2^m))⁻¹)*(a : CoefficientField m)⁻¹ =
      titsEnd m a*(a : CoefficientField m)⁻¹ := by
  rw [titsEnd_apply,pow_succ]
  simp only [Units.val_mul,Units.val_inv_eq_inv_val,mul_pow,inv_pow,mul_inv_rev,inv_inv]
  rw [pow_mul,pow_two]

/-- The h₁ action on the shifted whole Suzuki root; its center has the
corresponding norm weight, as required in (10.12). -/
theorem synchronizedLinearTorus_shiftedSuzuki (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 3) (x,y) *
        synchronizedLinearTorus Q split c a =
      synchronizedPositivePoint Q split c (.inr 3)
        ((titsEnd m a*(a : CoefficientField m)⁻¹)*x,
          (titsEnd m a*(a : CoefficientField m)⁻¹)*
            titsEnd m (titsEnd m a*(a : CoefficientField m)⁻¹)*y) := by
  let b : CoefficientField m := ((↑(a⁻¹*a⁻¹) : CoefficientField m)^(2^m))⁻¹
  have hb : b*(a : CoefficientField m)⁻¹ = titsEnd m a*(a : CoefficientField m)⁻¹ :=
    linear_shifted_weight a
  have hh := conjugate_right_product
    (synchronizedLinearTorus Q split c a)
    (synchronizedSuzukiTorus Q split c (a⁻¹*a⁻¹))
    (synchronizedPositivePoint Q split c (.inr 2) (x,y))
    (synchronizedPositivePoint Q split c (.inr 2)
      ((a : CoefficientField m)⁻¹*x,(a : CoefficientField m)⁻¹*(titsEnd m a)⁻¹*y))
    (synchronizedPositivePoint Q split c (.inr 2)
      ((titsEnd m a*(a : CoefficientField m)⁻¹)*x,
        (titsEnd m a*(a : CoefficientField m)⁻¹)*titsEnd m (titsEnd m a*(a : CoefficientField m)⁻¹)*y))
    (synchronizedLinearTorus_oppositeSuzuki Q split c a x y) (by
      rw [synchronizedSuzukiTorus_opposite]
      change synchronizedPositivePoint Q split c (.inr 2)
        (b*((a : CoefficientField m)⁻¹*x),
          b*titsEnd m b*((a : CoefficientField m)⁻¹*(titsEnd m a)⁻¹*y)) = _
      simp only [←hb,map_mul,map_inv₀]
      congr 1
      apply Prod.ext <;> dsimp only <;> ring)
  have he := conjugate_right_transport ((c.reflections 1).val : X ⧸ Q.D)
    (synchronizedLinearTorus Q split c a) _ _ _
    (synchronizedLinearTorus_suzukiReflection Q split c a) hh
  change (synchronizedLinearTorus Q split c a)⁻¹ *
    ((((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D)*
        (((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val))*_ = _
  simpa only [synchronizedPositivePoint_linear,synchronizedPositivePoint_suzuki,
    positiveLift,pinnedInput_reflections,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,Subgroup.coe_mul,
    mul_inv_rev,mul_assoc] using he

/-- The next linear root is the first reflected line conjugated by s₁. -/
theorem synchronizedLinearTorus_nextLinear (a : (CoefficientField m)ˣ)
    (x : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 2) x *
        synchronizedLinearTorus Q split c a =
      synchronizedPositivePoint Q split c (.inl 2) ((titsEnd m a)⁻¹*x) := by
  have hh := synchronizedLinearTorus_reflectedLinear Q split c a⁻¹ x
  rw [map_inv,inv_inv,Units.val_inv_eq_inv_val,map_inv₀] at hh
  have he := conjugate_right_transport ((c.reflections 0).val : X ⧸ Q.D)
    (synchronizedLinearTorus Q split c a) (synchronizedLinearTorus Q split c a)⁻¹
    _ _ (by simpa only [map_inv] using synchronizedLinearTorus_reflection Q split c a) (by
      simpa only [inv_inv] using hh)
  change (synchronizedLinearTorus Q split c a)⁻¹ *
    ((((c.reflections 1).val : X ⧸ Q.D)*(c.reflections 0).val)⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D)*
        (((c.reflections 1).val : X ⧸ Q.D)*(c.reflections 0).val))*_ = _
  simpa only [synchronizedPositivePoint_linear,synchronizedPositivePoint_suzuki,
    positiveLift,pinnedInput_reflections,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,Subgroup.coe_mul,
    mul_inv_rev,mul_assoc] using he

/-- The perpendicular Suzuki root has the reciprocal shifted-root weight under h₁. -/
theorem synchronizedLinearTorus_perpendicularSuzuki (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 1) (x,y) *
        synchronizedLinearTorus Q split c a =
      synchronizedPositivePoint Q split c (.inr 1)
        (((titsEnd m a)⁻¹*(a : CoefficientField m))*x,
          ((titsEnd m a)⁻¹*(a : CoefficientField m))*
            titsEnd m ((titsEnd m a)⁻¹*(a : CoefficientField m))*y) := by
  have hh := synchronizedLinearTorus_shiftedSuzuki Q split c a⁻¹ x y
  simp only [map_inv,inv_inv,Units.val_inv_eq_inv_val,map_inv₀] at hh
  have he := conjugate_right_transport ((c.reflections 0).val : X ⧸ Q.D)
    (synchronizedLinearTorus Q split c a) (synchronizedLinearTorus Q split c a)⁻¹
    _ _ (by simpa only [map_inv] using synchronizedLinearTorus_reflection Q split c a) (by
      simpa only [inv_inv] using hh)
  change (synchronizedLinearTorus Q split c a)⁻¹ *
    (((((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)*(c.reflections 0).val)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D)*
        ((((c.reflections 0).val : X ⧸ Q.D)*(c.reflections 1).val)*(c.reflections 0).val))*_ = _
  simpa only [synchronizedPositivePoint_linear,synchronizedPositivePoint_suzuki,
    positiveLift,pinnedInput_reflections,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,Subgroup.coe_mul,
    mul_inv_rev,mul_assoc] using he

include c in
private theorem rankOne_centralizes_perpendicularLinear_local :
    rankOne Q split 0 ≤ centralizer (positiveRoot Q split (.inl 3) : Set (X ⧸ Q.D)) := by
  have h0 : ⁅simpleRoot Q split 0,positiveRoot Q split (.inl 3)⁆ = ⊥ := by
    simpa only [nConj,U,Uat,OneMemClass.coe_one,rightConjugate_one,
      positiveRoot,positiveKind,positiveWord,Matrix.cons_val,Matrix.vecHead,Matrix.vecTail] using c.relations.ten_two_iv_left 1
  let s := (c.reflections 0).val
  have h1 : ⁅rightConjugate (simpleRoot Q split 0) (s : X ⧸ Q.D),
      positiveRoot Q split (.inl 3)⁆ = ⊥ := by
    have h := c.relations.ten_two_iv_left s
    change ⁅rightConjugate (simpleRoot Q split 0) (s : X ⧸ Q.D),
      rightConjugate (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) (s : X ⧸ Q.D)⁆ = ⊥ at h
    rw [perpendicular_root_stable Q split c.rotation_eight 0 1 (by decide)
      s (c.reflections 0).class_eq] at h
    exact h
  rw [rankOne_eq Q split 0 s (c.reflections 0).class_eq]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp h0)
    (commutator_eq_bot_iff_le_centralizer.mp h1)

/-- The final linear column of (10.12) is fixed by the first torus, since
its whole rank-one group centralizes the perpendicular linear root. -/
theorem synchronizedLinearTorus_perpendicularLinear (a : (CoefficientField m)ˣ)
    (x : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 3) x *
        synchronizedLinearTorus Q split c a =
      synchronizedPositivePoint Q split c (.inl 3) x := by
  have hr : synchronizedLinearTorus Q split c a ∈ rankOne Q split 0 :=
    (linearPinning Q split (pinnedInput Q split c)
      (Theory.PSL2.SemilinearCoverage.tor
        (Units.map (synchronizedField Q split c).toMonoidHom a))).property
  have hc := mem_centralizer_iff.mp (rankOne_centralizes_perpendicularLinear_local Q split c hr)
    _ (synchronizedPositiveChart Q split c (.inl 3) x).property
  change synchronizedPositivePoint Q split c (.inl 3) x*synchronizedLinearTorus Q split c a =
    synchronizedLinearTorus Q split c a*synchronizedPositivePoint Q split c (.inl 3) x at hc
  rw [mul_assoc,hc,inv_mul_cancel_left]

private theorem unit_square_root (b : (CoefficientField m)ˣ) :
    ∃ a : (CoefficientField m)ˣ, a*a = b := by
  obtain ⟨z,hz⟩ := FiniteField.isSquare_of_char_two
    (F := CoefficientField m) (ringChar.eq (CoefficientField m) 2) (b : CoefficientField m)
  have hz0 : z ≠ 0 := by
    intro he
    apply b.ne_zero
    simpa only [he,mul_zero] using hz
  refine ⟨Units.mk0 z hz0,?_⟩
  exact Units.ext hz.symm

private theorem linear_root_torus_quotient_centralizes (a b : (CoefficientField m)ˣ)
    (hab : a*a = b^(1+2^m)) :
    synchronizedSuzukiTorus Q split c b * (synchronizedLinearTorus Q split c a)⁻¹ ∈
      centralizer (rankOne Q split 0 : Set (X ⧸ Q.D)) := by
  let h := synchronizedSuzukiTorus Q split c b
  let k := synchronizedLinearTorus Q split c a
  have hH : h*k⁻¹ ∈ Q.tits.B ⊓ Q.tits.N :=
    (Q.tits.B ⊓ Q.tits.N).mul_mem (synchronizedSuzukiTorus_mem_cartan Q split c b)
      ((Q.tits.B ⊓ Q.tits.N).inv_mem (synchronizedLinearTorus_mem_cartan Q split c a))
  have hC : h*k⁻¹ ∈ centralizer (simpleRoot Q split 0 : Set (X ⧸ Q.D)) := by
    rw [mem_centralizer_iff]
    intro u hu
    obtain ⟨t,ht⟩ := (synchronizedLinearChart Q split c).surjective ⟨u,hu⟩
    have ht' : (synchronizedLinearChart Q split c t : X ⧸ Q.D) = u := congrArg Subtype.val ht
    have hpow : (a : CoefficientField m)^2 = (b : CoefficientField m)^(1+2^m) := by
      simpa only [Units.val_mul,Units.val_pow_eq_pow_val,pow_two] using congrArg Units.val hab
    have hw : h⁻¹*u*h = k⁻¹*u*k := by
      rw [←ht']
      change h⁻¹*(synchronizedLinearChart Q split c (.ofAdd t.toAdd) : X ⧸ Q.D)*h =
        k⁻¹*(synchronizedLinearChart Q split c (.ofAdd t.toAdd) : X ⧸ Q.D)*k
      rw [synchronizedSuzukiTorus_linear,synchronizedLinearTorus_simple,inv_pow,hpow]
    have hw' := congrArg (fun z : X ⧸ Q.D => h*z*k⁻¹) hw
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_inv_cancel,mul_one] using hw'
  have hh : h*k⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N) ⊓
      centralizer (simpleRoot Q split 0 : Set (X ⧸ Q.D)) := ⟨hH,hC⟩
  rw [cartan_centralizer_simpleRoot,←cartan_centralizer_rankOneRootGroup Q split 0] at hh
  exact hh.2

/-- The other cross-Weyl action follows from the exact linear-root weight. -/
theorem synchronizedSuzukiTorus_linearReflection (b : (CoefficientField m)ˣ) :
    ((c.reflections 0).val : X ⧸ Q.D)*synchronizedSuzukiTorus Q split c b*
      ((c.reflections 0).val : X ⧸ Q.D)⁻¹ =
      synchronizedSuzukiTorus Q split c b *
        synchronizedLinearTorus Q split c (b^(1+2^m))⁻¹ := by
  obtain ⟨a,ha⟩ := unit_square_root (b^(1+2^m))
  let s : X ⧸ Q.D := (c.reflections 0).val
  let h := synchronizedSuzukiTorus Q split c b
  let k := synchronizedLinearTorus Q split c a
  have hc : s*(h*k⁻¹) = (h*k⁻¹)*s :=
    mem_centralizer_iff.mp (linear_root_torus_quotient_centralizes Q split c a b ha)
      _ (c.reflections 0).mem_rankOne
  have hh : s*(h*k⁻¹)*s⁻¹ = h*k⁻¹ := by rw [hc,mul_inv_cancel_right]
  have hk : s*k*s⁻¹ = k⁻¹ := by
    simpa only [map_inv] using synchronizedLinearTorus_reflection Q split c a
  calc
    s*h*s⁻¹ = (s*(h*k⁻¹)*s⁻¹)*(s*k*s⁻¹) := by group
    _ = h*k⁻¹*k⁻¹ := by rw [hh,hk]
    _ = h*synchronizedLinearTorus Q split c (b^(1+2^m))⁻¹ := by
      rw [←ha,map_inv,map_mul]
      change h*k⁻¹*k⁻¹ = h*(k*k)⁻¹
      group

private theorem suzuki_next_weight (b : (CoefficientField m)ˣ) :
    titsEnd m (↑(b^(1+2^m))⁻¹ : CoefficientField m)*
      (b : CoefficientField m)^(1+2^m) = ((b : CoefficientField m)^(2^m))⁻¹ := by
  have ht : titsEnd m ((b : CoefficientField m)^(2^m)) = (b : CoefficientField m) :=
    ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates.titsEnd_halfFrobenius m b
  have hs : ((b : CoefficientField m)^(2^m))^2 = titsEnd m b :=
    ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates.halfFrobenius_sq m b
  have hpowinv : ((↑(b^(1+2^m))⁻¹ : CoefficientField m)) =
      ((b : CoefficientField m)^(1+2^m))⁻¹ := by
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  rw [hpowinv]
  simp only [map_inv₀,pow_add,pow_one,map_mul,ht,←hs]
  field_simp

theorem synchronizedSuzukiTorus_nextLinear (b : (CoefficientField m)ˣ)
    (x : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c b)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 2) x *
        synchronizedSuzukiTorus Q split c b =
      synchronizedPositivePoint Q split c (.inl 2) (((b : CoefficientField m)^(2^m))⁻¹*x) := by
  have hh := conjugate_right_product
    (synchronizedSuzukiTorus Q split c b)
    (synchronizedLinearTorus Q split c (b^(1+2^m))⁻¹)
    (synchronizedPositivePoint Q split c (.inl 1) x)
    (synchronizedPositivePoint Q split c (.inl 1) ((b : CoefficientField m)^(1+2^m)*x))
    (synchronizedPositivePoint Q split c (.inl 1) (((b : CoefficientField m)^(2^m))⁻¹*x))
    (synchronizedSuzukiTorus_reflectedLinear Q split c b x) (by
      rw [synchronizedLinearTorus_reflectedLinear,←mul_assoc,suzuki_next_weight])
  have he := conjugate_right_transport ((c.reflections 0).val : X ⧸ Q.D)
    (synchronizedSuzukiTorus Q split c b) _ _ _
    (synchronizedSuzukiTorus_linearReflection Q split c b) hh
  change (synchronizedSuzukiTorus Q split c b)⁻¹ *
    ((((c.reflections 1).val : X ⧸ Q.D)*(c.reflections 0).val)⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D)*
        (((c.reflections 1).val : X ⧸ Q.D)*(c.reflections 0).val))*_ = _
  simpa only [synchronizedPositivePoint_linear,synchronizedPositivePoint_suzuki,
    positiveLift,pinnedInput_reflections,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,Subgroup.coe_mul,
    mul_inv_rev,mul_assoc] using he

theorem synchronizedSuzukiTorus_perpendicularLinear (b : (CoefficientField m)ˣ)
    (x : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c b)⁻¹ *
      synchronizedPositivePoint Q split c (.inl 3) x *
        synchronizedSuzukiTorus Q split c b =
      synchronizedPositivePoint Q split c (.inl 3) ((b : CoefficientField m)^(2^m)*x) := by
  have hh := synchronizedSuzukiTorus_nextLinear Q split c b⁻¹ x
  simp only [map_inv,inv_inv,Units.val_inv_eq_inv_val,inv_pow] at hh
  have he := conjugate_right_transport ((c.reflections 1).val : X ⧸ Q.D)
    (synchronizedSuzukiTorus Q split c b) (synchronizedSuzukiTorus Q split c b)⁻¹
    _ _ (synchronizedSuzukiTorus_reflection Q split c b) (by
      simpa only [inv_inv] using hh)
  change (synchronizedSuzukiTorus Q split c b)⁻¹ *
    (((((c.reflections 1).val : X ⧸ Q.D)*(c.reflections 0).val)*(c.reflections 1).val)⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D)*
        ((((c.reflections 1).val : X ⧸ Q.D)*(c.reflections 0).val)*(c.reflections 1).val))*_ = _
  simpa only [synchronizedPositivePoint_linear,synchronizedPositivePoint_suzuki,
    positiveLift,pinnedInput_reflections,positiveWord,Matrix.cons_val,Fin.isValue,Matrix.head_cons,Subgroup.coe_mul,
    mul_inv_rev,mul_assoc] using he


/-- The two literal Cartan factors, with their synchronized source parameters. -/
def synchronizedTorus : (CoefficientField m)ˣ × (CoefficientField m)ˣ →* X ⧸ Q.D := by
  letI := split.abelian
  let h₁ := (synchronizedLinearTorus Q split c).codRestrict (Q.tits.B ⊓ Q.tits.N)
    (synchronizedLinearTorus_mem_cartan Q split c)
  let h₂ := (synchronizedSuzukiTorus Q split c).codRestrict (Q.tits.B ⊓ Q.tits.N)
    (synchronizedSuzukiTorus_mem_cartan Q split c)
  exact (Q.tits.B ⊓ Q.tits.N).subtype.comp
    ((h₁.comp (MonoidHom.fst _ _))*(h₂.comp (MonoidHom.snd _ _)))

@[simp] theorem synchronizedTorus_apply (a b : (CoefficientField m)ˣ) :
    synchronizedTorus Q split c (a,b) =
      synchronizedLinearTorus Q split c a*synchronizedSuzukiTorus Q split c b := rfl

theorem synchronizedTorus_mem_cartan (a b : (CoefficientField m)ˣ) :
    synchronizedTorus Q split c (a,b) ∈ Q.tits.B ⊓ Q.tits.N :=
  (Q.tits.B ⊓ Q.tits.N).mul_mem (synchronizedLinearTorus_mem_cartan Q split c a)
    (synchronizedSuzukiTorus_mem_cartan Q split c b)

theorem synchronizedTorus_injective : Function.Injective (synchronizedTorus Q split c) := by
  apply (synchronizedTorus Q split c).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  rintro ⟨a,b⟩ hab
  change synchronizedLinearTorus Q split c a*synchronizedSuzukiTorus Q split c b = 1 at hab
  have hc := conjugate_right_product
    (synchronizedLinearTorus Q split c a) (synchronizedSuzukiTorus Q split c b)
    (synchronizedPositivePoint Q split c (.inl 3) 1)
    (synchronizedPositivePoint Q split c (.inl 3) 1)
    (synchronizedPositivePoint Q split c (.inl 3) ((b : CoefficientField m)^(2^m)*1))
    (synchronizedLinearTorus_perpendicularLinear Q split c a 1)
    (synchronizedSuzukiTorus_perpendicularLinear Q split c b 1)
  rw [hab,inv_one,one_mul,mul_one,mul_one] at hc
  have hinj : Function.Injective (synchronizedPositivePoint Q split c (.inl 3)) :=
    Subtype.val_injective.comp (synchronizedPositiveChart Q split c (.inl 3)).injective
  have hb : b = 1 := by
    apply Units.ext
    apply iterateFrobenius_inj (CoefficientField m) 2 m
    change (b : CoefficientField m)^(2^m) = (1 : CoefficientField m)^(2^m)
    simpa only [one_pow] using (hinj hc).symm
  subst b
  rw [map_one,mul_one] at hab
  have ha := synchronizedLinearTorus_suzuki Q split c a 1 0
  rw [hab,inv_one,one_mul,mul_one,mul_one,mul_zero] at ha
  have hae := (suzukiChart Q split (pinnedInput Q split c)).injective (Subtype.ext ha)
  have haa : a = 1 := Units.ext (congrArg Prod.fst hae).symm
  subst a
  rfl

/-- The two constructed factors exhaust the entire original Cartan H. -/
theorem synchronizedTorus_range :
    (synchronizedTorus Q split c).range = Q.tits.B ⊓ Q.tits.N := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro h ⟨⟨a,b⟩,rfl⟩
    exact synchronizedTorus_mem_cartan Q split c a b
  · rw [←Nat.card_congr (MonoidHom.ofInjective (synchronizedTorus_injective Q split c)).toEquiv,
      Nat.card_prod,Nat.card_units,field_card,c.cartan_card,pow_two]

/-- A concrete full-Cartan coordinate equivalence for the later finite presentation. -/
def synchronizedCartanEquiv : (CoefficientField m)ˣ × (CoefficientField m)ˣ ≃*
    ↥(Q.tits.B ⊓ Q.tits.N) :=
  (MonoidHom.ofInjective (synchronizedTorus_injective Q split c)).trans
    (MulEquiv.subgroupCongr (synchronizedTorus_range Q split c))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
