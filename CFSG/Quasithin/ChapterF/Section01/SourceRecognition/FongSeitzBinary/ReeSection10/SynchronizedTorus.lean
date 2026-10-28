module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SynchronizedCommutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearTorus
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning

/-!
# Literal synchronized Ree torus actors and complete-root scalar actions

The linear diagonal is relabelled by the field automorphism forced by the
mixed V₁/V₂ comparison. The Suzuki diagonal uses the inverse matrix parameter,
so both actors follow the source's right-conjugation convention. They lie in
the original Cartan and have their exact diagonal actions on V₁, V₂ and Φ/Z.

The pinned Suzuki torus exhausts the faithful Cartan image on a whole root:
both have order q−1. Consequently every source Cartan element acts on each
reflected Suzuki root by (x,y) ↦ (a x, a theta(a) y). This includes q=2 and
removes any possible ambiguity in lifting a first-layer weight to its center.
As an actual consumer, the synchronized linear actor acts on the whole simple
Suzuki root with weights a and a theta(a), derived from its V₁ action.

Source: Fong–Seitz II (1974), printed pp.223–224, (10.10) and (10.12).
The remaining mixed and reflected table entries are developed separately.
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

def synchronizedLinearTorus : (CoefficientField m)ˣ →* X ⧸ Q.D :=
  (GTwoSource.alignedTorusHom Q split 0
    (linearRemainder_le_kernel Q split (pinnedInput Q split c))
    (linearLocalMarking Q split (pinnedInput Q split c)) (c.reflections 0)).comp
      (Units.map (synchronizedField Q split c).toMonoidHom)

@[simp] theorem synchronizedLinearTorus_apply (a : (CoefficientField m)ˣ) :
    synchronizedLinearTorus Q split c a =
      (linearPinning Q split (pinnedInput Q split c)
        (Theory.PSL2.SemilinearCoverage.tor
          (Units.map (synchronizedField Q split c).toMonoidHom a)) : X ⧸ Q.D) := rfl

theorem synchronizedLinearTorus_mem_cartan (a : (CoefficientField m)ˣ) :
    synchronizedLinearTorus Q split c a ∈ Q.tits.B ⊓ Q.tits.N :=
  GTwoSource.alignedTorus_mem_cartan Q split 0
    (linearRemainder_le_kernel Q split (pinnedInput Q split c))
    (linearLocalMarking Q split (pinnedInput Q split c)) (c.reflections 0) _

def matrixTorusParameterHom : (CoefficientField m)ˣ →* SuzukiSplitTorus m where
  toFun := matrixTorusParameter
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact BenderSuzuki.External.suzukiTorusGL_one m
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixTorusParameter,SuzukiTorusGL,SuzukiTorusMatrix,
        Matrix.mul_apply,Fin.sum_univ_four,mul_pow,mul_comm]

def synchronizedSuzukiTorus : (CoefficientField m)ˣ →* X ⧸ Q.D :=
  ((rankOne Q split 1).subtype.comp (pinnedSuzukiTorus Q split c)).comp
    (matrixTorusParameterHom.comp (MulEquiv.inv (CoefficientField m)ˣ).toMonoidHom)

@[simp] theorem synchronizedSuzukiTorus_apply (a : (CoefficientField m)ˣ) :
    synchronizedSuzukiTorus Q split c a =
      (pinnedSuzukiTorus Q split c (matrixTorusParameter a⁻¹) : X ⧸ Q.D) := rfl

theorem synchronizedSuzukiTorus_mem_cartan (a : (CoefficientField m)ˣ) :
    synchronizedSuzukiTorus Q split c a ∈ Q.tits.B ⊓ Q.tits.N :=
  pinnedSuzukiTorus_mem_cartan Q split c _

theorem synchronizedLinearTorus_simple (a : (CoefficientField m)ˣ) (t : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd t) : X ⧸ Q.D) *
        synchronizedLinearTorus Q split c a =
      synchronizedLinearChart Q split c (.ofAdd ((a : CoefficientField m)⁻¹^2*t)) := by
  have hh := GTwoSource.alignedTorus_root Q split 0
    (linearRemainder_le_kernel Q split (pinnedInput Q split c))
    (linearLocalMarking Q split (pinnedInput Q split c)) (c.reflections 0)
      (Units.map (synchronizedField Q split c).toMonoidHom a⁻¹)
      (synchronizedField Q split c t)
  change synchronizedLinearTorus Q split c a⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd t) : X ⧸ Q.D) *
        (synchronizedLinearTorus Q split c a⁻¹)⁻¹ = _ at hh
  rw [map_inv,inv_inv] at hh
  have he : (synchronizedField Q split c (↑a⁻¹ : CoefficientField m))^2 *
      synchronizedField Q split c t =
      synchronizedField Q split c ((a : CoefficientField m)⁻¹^2*t) := by
    simp only [Units.val_inv_eq_inv_val,map_mul,map_pow,map_inv₀]
  have hright := congrArg (fun z => GTwoSource.alignedSimpleParameter Q split 0
    (linearRemainder_le_kernel Q split (pinnedInput Q split c))
    (linearLocalMarking Q split (pinnedInput Q split c)) (c.reflections 0) (.ofAdd z)) he
  exact hh.trans hright

private theorem natural_torus (a : (CoefficientField m)ˣ)
    (v : Representation.SuzukiNatural.W m) :
    Representation.SuzukiNatural.natural m (matrixTorusParameter a) v =
      ![(a : CoefficientField m)^(1+2^m)*v 0,
        (a : CoefficientField m)^(2^m)*v 1,
        ((a : CoefficientField m)^(2^m))⁻¹*v 2,
        ((a : CoefficientField m)^(1+2^m))⁻¹*v 3] := by
  ext i
  fin_cases i <;> simp [Representation.SuzukiNatural.natural_apply,
    matrixTorusParameter,SuzukiTorusGL,SuzukiTorusMatrix,Matrix.mulVec,
    dotProduct,Fin.sum_univ_four]

theorem synchronizedSuzukiTorus_V2 (a : (CoefficientField m)ˣ)
    (v : (V2Section Q split (pinnedInput Q split c)).numerator) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      ((V2Section Q split (pinnedInput Q split c)).numeratorAction
        (pinnedSuzukiTorus Q split c (matrixTorusParameter a)) v))) =
      let x := V2Coordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk v))
      ![(a : CoefficientField m)^(1+2^m)*x 0,
        (a : CoefficientField m)^(2^m)*x 1,
        ((a : CoefficientField m)^(2^m))⁻¹*x 2,
        ((a : CoefficientField m)^(1+2^m))⁻¹*x 3] := by
  exact (V2Coordinates_source Q split (pinnedInput Q split c)
    (pinnedSuzukiTorus Q split c (matrixTorusParameter a)) v).trans
      (by rw [pinnedSuzukiTorus_model,natural_torus])

theorem synchronizedSuzukiTorus_phiCenter (a : (CoefficientField m)ˣ)
    (v : (phiCenterSection Q split (pinnedInput Q split c)).numerator) :
    phiCenterCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      ((phiCenterSection Q split (pinnedInput Q split c)).numeratorAction
        (pinnedSuzukiTorus Q split c (matrixTorusParameter a)) v))) =
      let x := phiCenterCoordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk v))
      ![(a : CoefficientField m)^(1+2^m)*x 0,
        (a : CoefficientField m)^(2^m)*x 1,
        ((a : CoefficientField m)^(2^m))⁻¹*x 2,
        ((a : CoefficientField m)^(1+2^m))⁻¹*x 3] := by
  rw [phiCenterCoordinates_source,pinnedSuzukiTorus_model,natural_torus]

private theorem suzuki_chart_actor (a b : CoefficientField m) :
    suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel
      (inclusion le_sup_left (suzukiChart Q split (pinnedInput Q split c) (a,b))) =
        (matrixRootPoint m a (b+a*titsEnd m a) : SuzukiMatrixGroup m) := by
  rw [suzukiActorEquiv_simpleRoot]
  change ((suzukiRootEquiv Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel)
    ((suzukiRootEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel).symm
      (matrixRootPoint m a (b+a*titsEnd m a))) : SuzukiMatrixGroup m) = _
  rw [MulEquiv.apply_symm_apply]

theorem pinnedSuzukiTorus_suzukiChart (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (pinnedSuzukiTorus Q split c (matrixTorusParameter a) : X ⧸ Q.D) *
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) *
        (pinnedSuzukiTorus Q split c (matrixTorusParameter a) : X ⧸ Q.D)⁻¹ =
      suzukiChart Q split (pinnedInput Q split c)
        ((a : CoefficientField m)*x,(a : CoefficientField m)*titsEnd m a*y) := by
  let e := suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel
  let r := pinnedSuzukiTorus Q split c (matrixTorusParameter a)
  let u := inclusion (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
    (suzukiChart Q split (pinnedInput Q split c) (x,y))
  let v := inclusion (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
    (suzukiChart Q split (pinnedInput Q split c)
      ((a : CoefficientField m)*x,(a : CoefficientField m)*titsEnd m a*y))
  have he : r*u*r⁻¹ = v := by
    apply e.injective
    rw [map_mul,map_mul,map_inv]
    rw [show e r = (matrixTorusParameter a : SuzukiMatrixGroup m) from
      pinnedSuzukiTorus_model Q split c _]
    have hu : e u = (matrixRootPoint m x (y+x*titsEnd m x) : SuzukiMatrixGroup m) :=
      suzuki_chart_actor Q split c x y
    have hv : e v = (matrixRootPoint m ((a : CoefficientField m)*x)
        ((a : CoefficientField m)*titsEnd m a*y+
          ((a : CoefficientField m)*x)*titsEnd m ((a : CoefficientField m)*x)) : SuzukiMatrixGroup m) :=
      suzuki_chart_actor Q split c _ _
    rw [hu,hv]
    apply Subtype.ext
    change SuzukiTorusGL m a * SuzukiRootGL m x (y+x*titsEnd m x) *
      (SuzukiTorusGL m a)⁻¹ = _
    rw [BenderSuzuki.External.suzukiTorusGL_conj_root m
      (suzukiTits m) (suzukiTits_sq m) (suzukiTits_apply m),
      NativeSuzukiChart.suzukiTits_eq_titsEnd,map_mul]
    congr 1
    ring
  exact congrArg Subtype.val he

theorem synchronizedSuzukiTorus_simple (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedSuzukiTorus Q split c a)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) *
        synchronizedSuzukiTorus Q split c a =
      suzukiChart Q split (pinnedInput Q split c)
        ((a : CoefficientField m)*x,(a : CoefficientField m)*titsEnd m a*y) := by
  rw [← map_inv]
  change (pinnedSuzukiTorus Q split c (matrixTorusParameter (a⁻¹)⁻¹) : X ⧸ Q.D) * _ * _ = _
  rw [inv_inv]
  have hi : (synchronizedSuzukiTorus Q split c a : X ⧸ Q.D) =
      (pinnedSuzukiTorus Q split c (matrixTorusParameter a) : X ⧸ Q.D)⁻¹ := by
    change ((rankOne Q split 1).subtype.comp (pinnedSuzukiTorus Q split c)
      |>.comp matrixTorusParameterHom) a⁻¹ = _
    rw [map_inv]
    rfl
  rw [hi]
  exact pinnedSuzukiTorus_suzukiChart Q split c a x y

/-- Every source Cartan element has a pure scalar action on the whole Suzuki root.
The complete faithful Cartan image has order q-1 and is exhausted by the pinned torus. -/
theorem cartan_suzukiChart_scalar (h : ↥(Q.tits.B ⊓ Q.tits.N)) :
    ∃ a : (CoefficientField m)ˣ, ∀ x y : CoefficientField m,
      (h : X ⧸ Q.D)*(suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D)*
        (h : X ⧸ Q.D)⁻¹ =
      suzukiChart Q split (pinnedInput Q split c)
        ((a : CoefficientField m)*x,(a : CoefficientField m)*titsEnd m a*y) := by
  let H := Q.tits.B ⊓ Q.tits.N
  let A := simpleRootAction Q split 1
  let f : (CoefficientField m)ˣ → A.range := fun a =>
    A.rangeRestrict ⟨pinnedSuzukiTorus Q split c (matrixTorusParameter a),
      pinnedSuzukiTorus_mem_cartan Q split c _⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he := congrArg (fun g : A.range =>
      ((g : MulAut (simpleRoot Q split 1))
        (suzukiChart Q split (pinnedInput Q split c) (1,0)) : X ⧸ Q.D)) hab
    change (pinnedSuzukiTorus Q split c (matrixTorusParameter a) : X ⧸ Q.D) *
      (suzukiChart Q split (pinnedInput Q split c) (1,0) : X ⧸ Q.D) *
        (pinnedSuzukiTorus Q split c (matrixTorusParameter a) : X ⧸ Q.D)⁻¹ =
      (pinnedSuzukiTorus Q split c (matrixTorusParameter b) : X ⧸ Q.D) *
      (suzukiChart Q split (pinnedInput Q split c) (1,0) : X ⧸ Q.D) *
        (pinnedSuzukiTorus Q split c (matrixTorusParameter b) : X ⧸ Q.D)⁻¹ at he
    rw [pinnedSuzukiTorus_suzukiChart,pinnedSuzukiTorus_suzukiChart] at he
    have hp := (suzukiChart Q split (pinnedInput Q split c)).injective (Subtype.ext he)
    exact Units.ext (by simpa only [mul_one] using congrArg Prod.fst hp)
  have hc : Nat.card A.range = Nat.card (CoefficientField m)ˣ := by
    rw [Nat.card_congr (simpleRootActionImageEquiv Q split 1).toEquiv,
      suzuki_cartanImage_card Q split 1 m c.suzuki c.suzukiBorel (c.reflections 1),
      Nat.card_units,GaloisField.card 2 (2*m+1) (by omega)]
  obtain ⟨a,ha⟩ := hf.bijective_of_nat_card_le hc.le |>.surjective (A.rangeRestrict h)
  refine ⟨a,fun x y => ?_⟩
  have he := congrArg (fun g : A.range =>
    ((g : MulAut (simpleRoot Q split 1))
      (suzukiChart Q split (pinnedInput Q split c) (x,y)) : X ⧸ Q.D)) ha
  exact he.symm.trans (pinnedSuzukiTorus_suzukiChart Q split c a x y)

/-- The same pure-scalar statement on each literal reflected whole Suzuki root. -/
theorem cartan_positiveSuzuki_scalar (h : ↥(Q.tits.B ⊓ Q.tits.N)) (j : Fin 4) :
    ∃ a : (CoefficientField m)ˣ, ∀ x y : CoefficientField m,
      (h : X ⧸ Q.D)*synchronizedPositivePoint Q split c (.inr j) (x,y)*
        (h : X ⧸ Q.D)⁻¹ =
      synchronizedPositivePoint Q split c (.inr j)
        ((a : CoefficientField m)*x,(a : CoefficientField m)*titsEnd m a*y) := by
  let s := positiveLift Q split (pinnedInput Q split c) (.inr j)
  let h' : ↥(Q.tits.B ⊓ Q.tits.N) :=
    ⟨(s : X ⧸ Q.D)*h*(s : X ⧸ Q.D)⁻¹,
      (mem_normalizer_iff.mp (torus_normalizes s) h).mp h.property⟩
  obtain ⟨a,ha⟩ := cartan_suzukiChart_scalar Q split c h'
  refine ⟨a,fun x y => ?_⟩
  have he := congrArg (fun z : X ⧸ Q.D => (s : X ⧸ Q.D)⁻¹*z*s) (ha x y)
  change (h : X ⧸ Q.D)*((s : X ⧸ Q.D)⁻¹*
    (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D)*s)*
    (h : X ⧸ Q.D)⁻¹ =
    (s : X ⧸ Q.D)⁻¹*(suzukiChart Q split (pinnedInput Q split c)
      ((a : CoefficientField m)*x,(a : CoefficientField m)*titsEnd m a*y) : X ⧸ Q.D)*s
  change (s : X ⧸ Q.D)⁻¹*(((s : X ⧸ Q.D)*h*(s : X ⧸ Q.D)⁻¹)*
    (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D)*
      ((s : X ⧸ Q.D)*h*(s : X ⧸ Q.D)⁻¹)⁻¹)*s = _ at he
  simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,
    mul_inv_cancel_left,mul_inv_cancel,inv_mul_cancel,mul_one] using he

/-- The synchronized linear torus has the exact two source natural weights. -/
theorem synchronizedLinearTorus_V1 (a : (CoefficientField m)ˣ)
    (v : (V1Section Q split (pinnedInput Q split c)).numerator) :
    V1BasisCoordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk
      ((V1Section Q split (pinnedInput Q split c)).numeratorAction
        (linearPinning Q split (pinnedInput Q split c)
          (Theory.PSL2.SemilinearCoverage.tor
            (Units.map (synchronizedField Q split c).toMonoidHom a⁻¹))) v))) =
      let x := V1BasisCoordinates Q split (pinnedInput Q split c)
        (Additive.ofMul (QuotientGroup.mk v))
      ![(synchronizedField Q split c (a : CoefficientField m))⁻¹*x 0,
        synchronizedField Q split c a*x 1] := by
  rw [V1BasisCoordinates_source,MulEquiv.symm_apply_apply,
    Representation.SL2.BinarySmall.natural_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    Theory.PSL2.SemilinearCoverage.tor,Units.val_inv_eq_inv_val]

theorem synchronizedLinearTorus_suzuki (a : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedLinearTorus Q split c a)⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) *
        synchronizedLinearTorus Q split c a =
      suzukiChart Q split (pinnedInput Q split c)
        ((a : CoefficientField m)*x,(a : CoefficientField m)*titsEnd m a*y) := by
  let d := pinnedInput Q split c
  let r := linearPinning Q split d (Theory.PSL2.SemilinearCoverage.tor
    (Units.map (synchronizedField Q split c).toMonoidHom a⁻¹))
  have hr : (r : X ⧸ Q.D) = (synchronizedLinearTorus Q split c a)⁻¹ := by
    rw [←map_inv]
    rfl
  obtain ⟨b,hb⟩ := cartan_suzukiChart_scalar Q split c
    ⟨(synchronizedLinearTorus Q split c a)⁻¹,
      (Q.tits.B ⊓ Q.tits.N).inv_mem (synchronizedLinearTorus_mem_cartan Q split c a)⟩
  let v := inclusion (simpleSuzuki_le_linearRemainder Q split d)
    (suzukiChart Q split d (1,0))
  have hv : (V1Section Q split d).numeratorAction r v =
      inclusion (simpleSuzuki_le_linearRemainder Q split d)
        (suzukiChart Q split d ((b : CoefficientField m),0)) := by
    apply Subtype.ext
    change (r : X ⧸ Q.D)*(suzukiChart Q split d (1,0) : X ⧸ Q.D)*
      (r : X ⧸ Q.D)⁻¹ = _
    rw [hr,inv_inv]
    simpa only [d,coe_inclusion,mul_one,mul_zero,inv_inv] using hb 1 0
  have hc := synchronizedLinearTorus_V1 Q split c a v
  rw [hv] at hc
  change V1BasisCoordinates Q split d (Additive.ofMul (V1SimpleRoot Q split d
    (suzukiChart Q split d ((b : CoefficientField m),0)))) =
      let z := V1BasisCoordinates Q split d (Additive.ofMul (V1SimpleRoot Q split d
        (suzukiChart Q split d (1,0))))
      ![(synchronizedField Q split c (a : CoefficientField m))⁻¹*z 0,
        synchronizedField Q split c a*z 1] at hc
  rw [V1BasisCoordinates_suzukiChart,V1BasisCoordinates_suzukiChart,V1BasisLabel_one] at hc
  have hba : b = a := by
    apply Units.ext
    apply (synchronizedField Q split c).injective
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,mul_one,synchronizedField_apply] using congrFun hc 1
  subst b
  simpa only [inv_inv] using hb x y

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
