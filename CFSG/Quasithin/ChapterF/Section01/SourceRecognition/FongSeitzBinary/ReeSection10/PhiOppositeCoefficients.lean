module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiCentralCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.MixedTorusTable

/-!
# Opposite omega coefficients in the literal Phi section

The supplied Suzuki reflection exchanges the two outer Phi lines and the two
linear lines. Its order-four product with the parameter-one root element
forces the remaining central coefficient. Torus transport and the native
triangular Suzuki multiplication then determine the action for every root
parameter, uniformly including the binary field.

Source: Fong--Seitz II (1974), (10.13)(ii), (10.16), and (10.17), pp.225--226.
The public theorem is an equality in the actual Phi numerator and retains the
chosen marked quotient, reflections, and triangular root chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4 BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
local notation "W" s:max => (sourceSimpleReflection Q split c s : X ⧸ Q.D)

section FiveAction
variable {E : Type*} [Group E] [IsElementaryAbelian 2 E]
private theorem inv_eq (x : E) : x⁻¹ = x := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) x
private theorem square (x : E) : x*x = 1 := by
  simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) x

private theorem elementary_fiveLine_orderFour (A B : MulAut E) (z h q p n o : E)
    (Az : A z = z) (Ah : A h = h) (Ap : A p = h*p)
    (An : A n = q*(h*p*n)) (Ao : A o = z*(h*n*o))
    (Bz : B z = z) (Bq : B q = q) (Bh : B h = o) (Bp : B p = n)
    (Bn : B n = p) (Bo : B o = h)
    (hfour : (B*A)^4 = 1) : z = q := by
  have hv := congrArg (fun f : MulAut E => f h) hfour
  simp only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] at hv
  simp only [map_mul,Az,Ah,Ap,An,Ao,Bz,Bq,Bh,Bp,Bn,Bo] at hv
  have hh : z*(q*h) = h := by
    calc
      _ = (z*z)*(z*z)*(o*o)*(o*o)*(o*o)*(p*p)*(p*p)*(h*h)*(n*n)*(z*(q*h)) := by
        simp only [square,one_mul]
      _ = _ := (show (z*z)*(z*z)*(o*o)*(o*o)*(o*o)*(p*p)*(p*p)*(h*h)*(n*n)*(z*(q*h)) =
        z * (z * (z * (o * p * h) * (o * n) * o) * (z * (o * p * h) * (q * (o * n * p))) * (z * (o * p * h))) from by ac_rfl).trans hv
  have hcancel := congrArg (fun x => x*h) hh
  simp only [mul_assoc,square,mul_one] at hcancel
  exact (eq_inv_iff_mul_eq_one.mpr hcancel).trans (inv_eq q)
end FiveAction

private theorem chart_actor (a b : CoefficientField m) :
    suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel
      (⟨(suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D),
        (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
          (suzukiChart Q split (pinnedInput Q split c) (a,b)).property⟩) =
        (matrixRootPoint m a (b+a*titsEnd m a) : SuzukiMatrixGroup m) := by
  have h := suzukiActorEquiv_simpleRoot Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel (suzukiChart Q split (pinnedInput Q split c) (a,b))
  apply h.trans
  change ((suzukiRootEquiv Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel)
    ((suzukiRootEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel).symm
      (matrixRootPoint m a (b+a*titsEnd m a))) : SuzukiMatrixGroup m) = _
  rw [MulEquiv.apply_symm_apply]

private theorem source_fourth_power :
    (⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩ *
      (⟨(suzukiChart Q split (pinnedInput Q split c) (1,0) : X ⧸ Q.D),
        (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
          (suzukiChart Q split (pinnedInput Q split c) (1,0)).property⟩ : rankOne Q split 1)) ^ 4 = 1 := by
  apply (suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel).injective
  rw [map_pow,map_mul,pinnedInput_reflection,chart_actor,map_one]
  simp only [map_one,mul_one,zero_add]
  apply Subtype.ext
  apply Units.ext
  change (SuzukiWeylMatrix m * SuzukiRootMatrix m 1 1)^4 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylMatrix,SuzukiRootMatrix,pow_succ,Matrix.mul_apply,Fin.sum_univ_four,
      CharTwo.add_self_eq_zero]

private theorem batch_pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_pair_word,MulAut.conj_apply] using hh

private theorem batch_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh

private def phiRootAction (a b : CoefficientField m) :
    MulAut (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
  (phiCenterSection Q split (pinnedInput Q split c)).numeratorAction
    (⟨((suzukiChart Q split (pinnedInput Q split c) (a,b))⁻¹ : X ⧸ Q.D),
      (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
        ((suzukiChart Q split (pinnedInput Q split c) (a,b))⁻¹).property⟩)

private def phiReflection : MulAut (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
  (phiCenterSection Q split (pinnedInput Q split c)).numeratorAction
    ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩

private theorem phiRootAction_eq (a b : CoefficientField m)
    (v : (phiCenterSection Q split (pinnedInput Q split c)).numerator) :
    phiRootAction Q split c a b v = v * phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b)) v := by
  change _ = v * (v⁻¹ * phiRootAction Q split c a b v)
  group

private theorem phiRootAction_central (a b y : CoefficientField m) :
    phiRootAction Q split c a b (phiCentralPoint Q split c y) = phiCentralPoint Q split c y := by
  apply Subtype.ext
  have hc := mem_centralizer_iff.mp
    (rankOne_centralizes_perpendicularSuzuki Q split c
      ((show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
        (suzukiChart Q split (pinnedInput Q split c) (a,b)).property))
    (S 1 0 y) (synchronizedPositiveChart Q split c (.inr 1) (0,y)).property
  change (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
    S 1 0 y * ((suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹)⁻¹ = _
  change _ = S 1 0 y
  have hh : Commute (S 1 0 y) (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := hc
  rw [←hh.inv_right.eq]
  simp only [mul_assoc,mul_inv_cancel,mul_one]

private theorem phiRootAction_shifted (a b y : CoefficientField m) :
    phiRootAction Q split c a b (phiShiftedPoint Q split c y) = phiShiftedPoint Q split c y := by
  apply Subtype.ext
  have h := synchronized_ten_eight Q split c a b 0 y
  simp only [mul_zero,synchronizedPositivePoint_pair_zero] at h
  change (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
    S 3 0 y * ((suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹)⁻¹ = _
  change _ = S 3 0 y
  have hh := congrArg (fun v => S 3 0 y * v) h
  simpa only [mul_assoc,mul_inv_cancel_left,mul_one,inv_inv] using hh

private theorem phiRootAction_perpendicular (a b y : CoefficientField m) :
    phiRootAction Q split c a b (phiPerpendicularPoint Q split c y) =
      phiShiftedPoint Q split c (a*y) * phiPerpendicularPoint Q split c y := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator := phiRemainder_elementary Q split (pinnedInput Q split c)
  rw [phiRootAction_eq]
  have he : phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b)) (phiPerpendicularPoint Q split c y) =
      phiShiftedPoint Q split c (a*y) := by
    apply Subtype.ext
    rw [phiRightCommutator_val]
    exact synchronized_ten_eleven_i Q split c a b y
  rw [he,mul_comm]

private theorem phiRootAction_next (a b y : CoefficientField m) :
    phiRootAction Q split c a b (phiNextPoint Q split c y) =
      phiCentralPoint Q split c (a*titsEnd m y) *
        (phiShiftedPoint Q split c (b*y) * phiPerpendicularPoint Q split c (titsEnd m a*y) *
          phiNextPoint Q split c y) := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator := phiRemainder_elementary Q split (pinnedInput Q split c)
  rw [phiRootAction_eq,synchronized_nextLinear_commutator]
  ac_rfl

private theorem phiReflection_central (y : CoefficientField m) :
    phiReflection Q split c (phiCentralPoint Q split c y) = phiCentralPoint Q split c y := by
  apply Subtype.ext
  change MulAut.conj (W true) (S 1 0 y) = S 1 0 y
  exact batch_quartet_reflection Q split c true 1 (by decide) 0 y

private theorem phiReflection_shifted (y : CoefficientField m) :
    phiReflection Q split c (phiShiftedPoint Q split c y) = phiOppositeOmega Q split (pinnedInput Q split c) y := by
  apply Subtype.ext
  rw [phiOppositeOmega_point]
  change MulAut.conj (W true) (S 3 0 y) = S 2 0 y
  exact batch_quartet_reflection Q split c true 3 (by decide) 0 y

private theorem phiReflection_opposite (y : CoefficientField m) :
    phiReflection Q split c (phiOppositeOmega Q split (pinnedInput Q split c) y) = phiShiftedPoint Q split c y := by
  apply Subtype.ext
  change MulAut.conj (W true) (phiOppositeOmega Q split (pinnedInput Q split c) y) = S 3 0 y
  rw [phiOppositeOmega_point]
  exact batch_quartet_reflection Q split c true 2 (by decide) 0 y

private theorem phiReflection_perpendicular (y : CoefficientField m) :
    phiReflection Q split c (phiPerpendicularPoint Q split c y) = phiNextPoint Q split c y := by
  apply Subtype.ext
  change MulAut.conj (W true) (L 3 y) = L 2 y
  exact batch_pair_reflection Q split c true 3 (by decide) y

private theorem phiReflection_next (y : CoefficientField m) :
    phiReflection Q split c (phiNextPoint Q split c y) = phiPerpendicularPoint Q split c y := by
  apply Subtype.ext
  change MulAut.conj (W true) (L 2 y) = L 3 y
  exact batch_pair_reflection Q split c true 2 (by decide) y

private theorem phiActions_four :
    (phiReflection Q split c * phiRootAction Q split c 1 1)^4 = 1 := by
  have hu : (suzukiChart Q split (pinnedInput Q split c) (1,1))⁻¹ =
      suzukiChart Q split (pinnedInput Q split c) (1,0) := by
    rw [suzukiChart_inverse]
    simp only [map_one,mul_one,CharTwo.add_self_eq_zero]
  have hr : (⟨((suzukiChart Q split (pinnedInput Q split c) (1,1))⁻¹ : X ⧸ Q.D),
      (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
        ((suzukiChart Q split (pinnedInput Q split c) (1,1))⁻¹).property⟩ : rankOne Q split 1) =
      ⟨(suzukiChart Q split (pinnedInput Q split c) (1,0) : X ⧸ Q.D),
        (show simpleRoot Q split 1 ≤ rankOne Q split 1 from le_sup_left)
          (suzukiChart Q split (pinnedInput Q split c) (1,0)).property⟩ :=
    Subtype.ext (congrArg (fun z : simpleRoot Q split 1 => (z : X ⧸ Q.D)) hu)
  unfold phiReflection phiRootAction
  rw [hr]
  have h := congrArg (phiCenterSection Q split (pinnedInput Q split c)).numeratorAction
    (source_fourth_power Q split c)
  simpa only [map_pow,map_mul,map_one] using h


private theorem phiPerpendicular_zero : phiPerpendicularPoint Q split c 0 = 1 := by
  apply Subtype.ext
  exact synchronizedPositivePoint_pair_zero Q split c 3

private theorem phiCentral_injective : Function.Injective (phiCentralPoint Q split c) := by
  intro a b h
  have hh := congrArg (fun v : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    (v : X ⧸ Q.D)) h
  have he := (synchronizedPositiveChart Q split c (.inr 1)).injective (Subtype.ext hh)
  exact congrArg Prod.snd he

private theorem phi_unit_opposite (y : CoefficientField m) :
    phiRootAction Q split c 1 1 (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiCentralPoint Q split c (titsEnd m y) *
        (phiShiftedPoint Q split c y * phiNextPoint Q split c y *
          phiOppositeOmega Q split (pinnedInput Q split c) y) := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  obtain ⟨z,hz⟩ := synchronized_opposite_central_lift_public Q split c 1 1 y
  simp only [one_pow,map_one,mul_one,CharTwo.add_self_eq_zero,zero_add,
    zero_mul,one_mul,phiPerpendicular_zero,mul_one] at hz
  have ho : phiRootAction Q split c 1 1 (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiCentralPoint Q split c z *
        (phiShiftedPoint Q split c y * phiNextPoint Q split c y *
          phiOppositeOmega Q split (pinnedInput Q split c) y) := by
    rw [phiRootAction_eq,hz]
    ac_rfl
  have hz' : phiCentralPoint Q split c z = phiCentralPoint Q split c (titsEnd m y) :=
    elementary_fiveLine_orderFour (phiRootAction Q split c 1 1) (phiReflection Q split c)
      (phiCentralPoint Q split c z) (phiShiftedPoint Q split c y)
      (phiCentralPoint Q split c (titsEnd m y)) (phiPerpendicularPoint Q split c y)
      (phiNextPoint Q split c y) (phiOppositeOmega Q split (pinnedInput Q split c) y)
      (phiRootAction_central Q split c 1 1 z) (phiRootAction_shifted Q split c 1 1 y)
      (by simpa only [one_mul] using phiRootAction_perpendicular Q split c 1 1 y)
      (by simpa only [one_mul,map_one] using phiRootAction_next Q split c 1 1 y)
      ho (phiReflection_central Q split c z) (phiReflection_central Q split c (titsEnd m y))
      (phiReflection_shifted Q split c y) (phiReflection_perpendicular Q split c y)
      (phiReflection_next Q split c y) (phiReflection_opposite Q split c y)
      (phiActions_four Q split c)
  rw [hz'] at ho
  exact ho

private theorem phiRootAction_mul (a b e f : CoefficientField m) :
    phiRootAction Q split c (a+e) (b+f+titsEnd m a*e) =
      phiRootAction Q split c e f * phiRootAction Q split c a b := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change ((suzukiChart Q split (pinnedInput Q split c) (a+e,b+f+titsEnd m a*e) : X ⧸ Q.D)⁻¹ *
    (v : X ⧸ Q.D) * ((suzukiChart Q split (pinnedInput Q split c) (a+e,b+f+titsEnd m a*e) : X ⧸ Q.D)⁻¹)⁻¹) = _
  rw [←suzukiChart_mul,Subgroup.coe_mul]
  change _ = (suzukiChart Q split (pinnedInput Q split c) (e,f) : X ⧸ Q.D)⁻¹ *
    ((suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ * (v : X ⧸ Q.D) *
      ((suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹)⁻¹) *
        ((suzukiChart Q split (pinnedInput Q split c) (e,f) : X ⧸ Q.D)⁻¹)⁻¹
  group

private theorem phiCentral_zero : phiCentralPoint Q split c 0 = 1 := by
  apply Subtype.ext
  exact synchronizedPositivePoint_quartet_zero Q split c 1

private theorem phi_omega_opposite (b y : CoefficientField m) :
    phiRootAction Q split c 0 b (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiCentralPoint Q split c (b*titsEnd m y) *
        (phiShiftedPoint Q split c (titsEnd m b*y) * phiPerpendicularPoint Q split c (b*y) *
          phiOppositeOmega Q split (pinnedInput Q split c) y) := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  rw [phiRootAction_eq,synchronized_omega_omega_commutator]
  ac_rfl

/-- The parameter-one central correction follows from the supplied order-four
Suzuki action on the five literal elementary Phi root lines. -/
private theorem synchronizedPhi_pure_unit_action (y : CoefficientField m) :
    phiRootAction Q split c 1 0 (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiShiftedPoint Q split c y * phiPerpendicularPoint Q split c y *
        phiNextPoint Q split c y * phiOppositeOmega Q split (pinnedInput Q split c) y := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  have h := congrArg (phiRootAction Q split c 0 1) (phi_unit_opposite Q split c y)
  have ha : phiRootAction Q split c 1 0 = phiRootAction Q split c 0 1 * phiRootAction Q split c 1 1 := by
    simpa only [add_zero,map_one,mul_zero,CharTwo.add_self_eq_zero] using phiRootAction_mul Q split c 1 1 0 1
  change (phiRootAction Q split c 0 1 * phiRootAction Q split c 1 1)
    (phiOppositeOmega Q split (pinnedInput Q split c) y) = _ at h
  rw [←ha] at h
  simp only [map_mul,phiRootAction_central,phiRootAction_shifted,phiRootAction_next,
    phi_omega_opposite,zero_mul,map_zero,map_one,one_mul,phiCentral_zero,phiPerpendicular_zero,
    one_mul,mul_one] at h
  apply h.trans
  calc
    _ = (phiCentralPoint Q split c (titsEnd m y) * phiCentralPoint Q split c (titsEnd m y)) *
        (phiShiftedPoint Q split c y * phiShiftedPoint Q split c y) *
        (phiShiftedPoint Q split c y * phiPerpendicularPoint Q split c y *
          phiNextPoint Q split c y * phiOppositeOmega Q split (pinnedInput Q split c) y) := by ac_rfl
    _ = _ := by rw [square,square,one_mul,one_mul]

private theorem phi_pure_unit_commutator (y : CoefficientField m) :
    (S 2 0 y)⁻¹ * (suzukiChart Q split (pinnedInput Q split c) (1,0) : X ⧸ Q.D)⁻¹ *
      S 2 0 y * (suzukiChart Q split (pinnedInput Q split c) (1,0) : X ⧸ Q.D) =
      S 3 0 y * L 3 y * L 2 y := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  have hd : phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (1,0))
      (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiShiftedPoint Q split c y * phiPerpendicularPoint Q split c y * phiNextPoint Q split c y := by
    apply mul_left_cancel (a := phiOppositeOmega Q split (pinnedInput Q split c) y)
    rw [←phiRootAction_eq,synchronizedPhi_pure_unit_action]
    ac_rfl
  have hv := congrArg (fun v : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    (v : X ⧸ Q.D)) hd
  rw [phiRightCommutator_val,phiOppositeOmega_point] at hv
  exact hv

private theorem phi_pure_commutator (a y : CoefficientField m) :
    (S 2 0 y)⁻¹ * (suzukiChart Q split (pinnedInput Q split c) (a,0) : X ⧸ Q.D)⁻¹ *
      S 2 0 y * (suzukiChart Q split (pinnedInput Q split c) (a,0) : X ⧸ Q.D) =
      S 3 0 (a^2*titsEnd m a*y) * L 3 (a*titsEnd m a*y) * L 2 (a*y) := by
  by_cases ha : a = 0
  · subst a
    simp only [suzukiChart_zero,OneMemClass.coe_one,inv_one,mul_one,inv_mul_cancel,
      zero_pow (by decide : 2 ≠ 0),zero_mul,synchronizedPositivePoint_quartet_zero,
      synchronizedPositivePoint_pair_zero]
  let u : (CoefficientField m)ˣ := Units.mk0 a ha
  let t := synchronizedLinearTorus Q split c u
  let e := MulAut.conj t⁻¹
  have he (x : X ⧸ Q.D) : e x = t⁻¹*x*t := by
    simp only [e,MulAut.conj_apply,inv_inv]
  have h := congrArg e (phi_pure_unit_commutator Q split c (a*titsEnd m a*y))
  simp only [map_mul,map_inv] at h
  simp only [he] at h
  dsimp only [t] at h
  rw [synchronizedLinearTorus_oppositeSuzuki,synchronizedLinearTorus_suzuki,
    synchronizedLinearTorus_shiftedSuzuki,synchronizedLinearTorus_perpendicularLinear,
    synchronizedLinearTorus_nextLinear] at h
  have ht : titsEnd m a ≠ 0 := by
    intro hzero
    apply ha
    exact (titsEnd m).injective (hzero.trans (map_zero _).symm)
  have hback : (a⁻¹*(titsEnd m a)⁻¹)*(a*titsEnd m a*y) = y := by field_simp
  have hmiddle : (titsEnd m a)⁻¹ * (a*titsEnd m a*y) = a*y := by field_simp
  have hweight : (titsEnd m a*a⁻¹)*titsEnd m (titsEnd m a*a⁻¹) = a := by
    rw [map_mul,map_inv₀,titsEnd_twice]
    field_simp
  simp only [u,Units.val_mk0,mul_one,mul_zero] at h
  rw [hback,hmiddle,hweight] at h
  convert h using 1; ring_nf

private theorem phiRootAction_pure (a y : CoefficientField m) :
    phiRootAction Q split c a 0 (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiShiftedPoint Q split c (a^2*titsEnd m a*y) *
        phiPerpendicularPoint Q split c (a*titsEnd m a*y) * phiNextPoint Q split c (a*y) *
          phiOppositeOmega Q split (pinnedInput Q split c) y := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  have hd : phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,0))
      (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiShiftedPoint Q split c (a^2*titsEnd m a*y) *
        phiPerpendicularPoint Q split c (a*titsEnd m a*y) * phiNextPoint Q split c (a*y) := by
    apply Subtype.ext
    rw [phiRightCommutator_val,phiOppositeOmega_point]
    exact phi_pure_commutator Q split c a y
  rw [phiRootAction_eq,hd]
  ac_rfl

private theorem phiShifted_add (x y : CoefficientField m) :
    phiShiftedPoint Q split c x * phiShiftedPoint Q split c y = phiShiftedPoint Q split c (x+y) := by
  apply Subtype.ext
  change S 3 0 x * S 3 0 y = S 3 0 (x+y)
  simpa only [zero_add,map_zero,zero_mul,add_zero] using
    synchronizedPositivePoint_quartet_mul Q split c 3 0 x 0 y

private theorem phiPerpendicular_add (x y : CoefficientField m) :
    phiPerpendicularPoint Q split c x * phiPerpendicularPoint Q split c y =
      phiPerpendicularPoint Q split c (x+y) := by
  apply Subtype.ext
  exact synchronizedPositivePoint_pair_mul Q split c 3 x y

/-- The full central coefficient in the opposite-Omega action, with the native
triangular correction and all coefficient fields, including q=2. -/
theorem synchronized_oppositeOmega_commutator (a b y : CoefficientField m) :
    phiRightCommutator Q split (pinnedInput Q split c)
      (suzukiChart Q split (pinnedInput Q split c) (a,b))
      (phiOppositeOmega Q split (pinnedInput Q split c) y) =
    phiCentralPoint Q split c (b*titsEnd m y) *
      (phiShiftedPoint Q split c ((a^2*titsEnd m a+a*b+titsEnd m b)*y) *
        phiPerpendicularPoint Q split c ((b+a*titsEnd m a)*y) * phiNextPoint Q split c (a*y)) := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  have ha : phiRootAction Q split c a b = phiRootAction Q split c 0 b * phiRootAction Q split c a 0 := by
    simpa only [add_zero,zero_add,mul_zero] using phiRootAction_mul Q split c a 0 0 b
  have h := congrArg (phiRootAction Q split c 0 b) (phiRootAction_pure Q split c a y)
  change (phiRootAction Q split c 0 b * phiRootAction Q split c a 0)
    (phiOppositeOmega Q split (pinnedInput Q split c) y) = _ at h
  rw [←ha] at h
  simp only [map_mul,phiRootAction_shifted,phiRootAction_perpendicular,phiRootAction_next,
    phi_omega_opposite,zero_mul,map_zero,phiCentral_zero,phiPerpendicular_zero,
    one_mul,mul_one] at h
  have hs0 : phiShiftedPoint Q split c 0 = 1 := by
    apply Subtype.ext
    exact synchronizedPositivePoint_quartet_zero Q split c 3
  rw [hs0,one_mul] at h
  have hformula : phiRootAction Q split c a b (phiOppositeOmega Q split (pinnedInput Q split c) y) =
      phiCentralPoint Q split c (b*titsEnd m y) *
        (phiShiftedPoint Q split c ((a^2*titsEnd m a+a*b+titsEnd m b)*y) *
          phiPerpendicularPoint Q split c ((b+a*titsEnd m a)*y) * phiNextPoint Q split c (a*y)) *
            phiOppositeOmega Q split (pinnedInput Q split c) y := by
    apply h.trans
    calc
      _ = phiCentralPoint Q split c (b*titsEnd m y) *
          ((phiShiftedPoint Q split c (a^2*titsEnd m a*y) * phiShiftedPoint Q split c (b*(a*y)) *
              phiShiftedPoint Q split c (titsEnd m b*y)) *
            (phiPerpendicularPoint Q split c (a*titsEnd m a*y) * phiPerpendicularPoint Q split c (b*y)) *
              phiNextPoint Q split c (a*y)) * phiOppositeOmega Q split (pinnedInput Q split c) y := by ac_rfl
      _ = _ := by
        rw [phiShifted_add,phiShifted_add,phiPerpendicular_add]
        have h1 : (a^2*titsEnd m a*y+b*(a*y))+titsEnd m b*y =
            (a^2*titsEnd m a+a*b+titsEnd m b)*y := by ring
        have h2 : a*titsEnd m a*y+b*y = (b+a*titsEnd m a)*y := by ring
        rw [h1,h2]
  apply mul_left_cancel (a := phiOppositeOmega Q split (pinnedInput Q split c) y)
  rw [←phiRootAction_eq,hformula]
  ac_rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
