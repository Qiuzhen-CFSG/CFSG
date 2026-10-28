module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SignedEquations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SynchronizedTorus
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.FourDimensional
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.GlobalRealizations
/-!
# Literal linear and Suzuki Gauss transport

The two finite Gauss factorizations are transported from the checked PSL₂ and
four-dimensional Suzuki matrix calculations through the supplied pinnings. The
resulting equations live in the original source quotient and use the literal
reflection lifts and synchronized charts. The final source consumers retain
only the exact Cartan normalizations as hypotheses for the assembled `T.h`; no
model relation or source Gauss equation is assumed.

Source: Fong--Seitz II (1974), (10.10)--(10.12); GLS3 2.3.4--8, Table 2.4.
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
open ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
private theorem norm_tits (a b : CoefficientField m) :
    norm (titsEnd m a) (titsEnd m b) = titsEnd m (norm a b) := by
  simp only [ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.norm,map_add,map_mul,theta_tits,tits_theta]
private theorem negativeFirst_tits (a b : CoefficientField m) :
    negativeFirst (titsEnd m a) (titsEnd m b) = titsEnd m (negativeFirst a b) := by
  simp only [negativeFirst,norm_tits,map_div₀]
private theorem negativeSecond_tits (a b : CoefficientField m) :
    negativeSecond (titsEnd m a) (titsEnd m b) = titsEnd m (negativeSecond a b) := by
  simp only [negativeSecond,norm_tits,map_div₀]
private theorem positiveFirst_tits (a b : CoefficientField m) :
    positiveFirst (titsEnd m a) (titsEnd m b) = titsEnd m (positiveFirst a b) := by
  simp only [positiveFirst,norm_tits,map_div₀,map_add,map_mul]
private theorem positiveSecond_tits (a b : CoefficientField m) :
    positiveSecond (titsEnd m a) (titsEnd m b) = titsEnd m (positiveSecond a b) := by
  simp only [positiveSecond,negativeSecond_tits,positiveFirst_tits,map_add,map_mul]
private theorem fourWord_tits (a b : CoefficientField m) :
    fourWord true (titsEnd m a) (titsEnd m b) = SuzukiRootMatrix m a (b+a*titsEnd m a) := by
  rw [fourWord_positive]
  simp only [standardPair,Equiv.coe_fn_mk,theta_tits]
  congr 1
  ring
/-- Parameter of the actual synchronized Suzuki torus in the Gauss decomposition. -/
def synchronizedSuzukiGaussParameter (a : (CoefficientField m)ˣ) : (CoefficientField m)ˣ :=
  (a / Units.map (titsEnd m).toMonoidHom a)^2

@[simp] theorem synchronizedSuzukiGaussParameter_coe (a : (CoefficientField m)ˣ) :
    (synchronizedSuzukiGaussParameter a : CoefficientField m) =
      ((a : CoefficientField m) / titsEnd m a)^2 := by
  simp [synchronizedSuzukiGaussParameter, Units.val_pow_eq_pow_val, div_eq_mul_inv]

@[simp] theorem synchronizedSuzukiGaussParameter_inv_coe (a : (CoefficientField m)ˣ) :
    ((synchronizedSuzukiGaussParameter a)⁻¹ : CoefficientField m) =
      (titsEnd m (a : CoefficientField m) / a)^2 := by
  simp [synchronizedSuzukiGaussParameter, Units.val_pow_eq_pow_val, div_eq_mul_inv]
  field_simp
private theorem fourTorus_tits (a : (CoefficientField m)ˣ) :
    fourTorus (titsEnd m (a : CoefficientField m)) =
      SuzukiTorusMatrix m (synchronizedSuzukiGaussParameter a)⁻¹ := by
  have ha := a.ne_zero
  have hpa := (map_ne_zero (titsEnd m)).mpr ha
  have he : ((synchronizedSuzukiGaussParameter a)⁻¹ : (CoefficientField m)ˣ) =
      (Units.map (titsEnd m).toMonoidHom a / a)^2 := by
    apply Units.ext
    simp [synchronizedSuzukiGaussParameter, div_eq_mul_inv]
    field_simp
  rw [he]
  have hmid : (((titsEnd m (a : CoefficientField m) / a)^2))^(2^m) =
      (a : CoefficientField m)^2/titsEnd m a := by
    rw [←show ∀ z : CoefficientField m, theta m z = z^(2^m) from fun _ => rfl]
    rw [map_pow,map_div₀,theta_tits,div_pow,theta_sq]
  have htop : (((titsEnd m (a : CoefficientField m) / a)^2))^(1+2^m) =
      titsEnd m a := by
    rw [pow_add,pow_one,hmid]
    field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourTorus,SuzukiTorusMatrix,Units.val_pow_eq_pow_val,Units.val_div_eq_div_val,
      hmid,htop,titsEnd_twice]
private theorem synchronizedSuzuki_matrix_gauss (a b : CoefficientField m)
    (hn : norm a b ≠ 0) :
    (suzukiWeyl m : SuzukiMatrixGroup m) *
      (suzukiWeyl m * (matrixRootPoint m a (b+a*titsEnd m a) : SuzukiMatrixGroup m) *
        (suzukiWeyl m)⁻¹) =
      (suzukiWeyl m * (matrixRootPoint m (negativeFirst a b)
        (negativeSecond a b+negativeFirst a b*titsEnd m (negativeFirst a b)) : SuzukiMatrixGroup m) *
          (suzukiWeyl m)⁻¹) *
        (matrixTorusParameter (synchronizedSuzukiGaussParameter (Units.mk0 (norm a b) hn))⁻¹ : SuzukiMatrixGroup m) *
          matrixRootPoint m (positiveFirst a b)
            (positiveSecond a b+positiveFirst a b*titsEnd m (positiveFirst a b)) := by
  have h := four_gauss (titsEnd m a) (titsEnd m b)
    (by rw [norm_tits]; exact (map_ne_zero (titsEnd m)).mpr hn)
  rw [negativeFirst_tits,negativeSecond_tits,positiveFirst_tits,positiveSecond_tits,
    norm_tits,fourWord_negative,fourWord_negative,fourWord_tits,fourWord_tits,fourWord_tits] at h
  have htor := fourTorus_tits (m := m) (Units.mk0 (norm a b) hn)
  change fourTorus (titsEnd m (norm a b)) =
    SuzukiTorusMatrix m (synchronizedSuzukiGaussParameter (Units.mk0 (norm a b) hn))⁻¹ at htor
  rw [htor] at h
  rw [inv_eq_of_mul_eq_one_right (suzukiWeyl_sq m)]
  apply Subtype.ext
  apply Units.ext
  exact h

private theorem synchronizedSuzuki_chart_actor (a b : CoefficientField m) :
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

theorem synchronizedSuzuki_gauss (a b : CoefficientField m)
    (hn : norm a b ≠ 0) :
    ((c.reflections 1).val : X ⧸ Q.D) *
      (((c.reflections 1).val : X ⧸ Q.D) *
        (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) *
          ((c.reflections 1).val : X ⧸ Q.D)⁻¹) =
      (((c.reflections 1).val : X ⧸ Q.D) *
        (suzukiChart Q split (pinnedInput Q split c)
          (negativeFirst a b, negativeSecond a b) : X ⧸ Q.D) *
          ((c.reflections 1).val : X ⧸ Q.D)⁻¹) *
        synchronizedSuzukiTorus Q split c
          (synchronizedSuzukiGaussParameter (Units.mk0 (norm a b) hn)) *
        (suzukiChart Q split (pinnedInput Q split c)
          (positiveFirst a b, positiveSecond a b) : X ⧸ Q.D) := by
  let e := suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel
  let f : SuzukiMatrixGroup m →* X ⧸ Q.D :=
    (rankOne Q split 1).subtype.comp e.symm.toMonoidHom
  have h := congrArg f (synchronizedSuzuki_matrix_gauss (m := m) a b hn)
  simp only [map_mul, map_inv] at h
  have hw : f (suzukiWeyl m) = ((c.reflections 1).val : X ⧸ Q.D) := by
    change (e.symm (suzukiWeyl m) : X ⧸ Q.D) = _
    rw [← pinnedInput_reflection Q split c]
    change (e.symm (e _) : X ⧸ Q.D) = _
    rw [e.symm_apply_apply]
  have hu (x y : CoefficientField m) :
      f (matrixRootPoint m x (y+x*titsEnd m x)) =
        (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) := by
    have hh := synchronizedSuzuki_chart_actor Q split c x y
    change (e.symm (matrixRootPoint m x (y+x*titsEnd m x)) : X ⧸ Q.D) = _
    rw [← hh]
    have he := e.symm_apply_apply
      (inclusion le_sup_left (suzukiChart Q split (pinnedInput Q split c) (x,y)))
    exact congrArg Subtype.val he
  rw [hw, hu, hu, hu] at h
  exact h

open ReeF4.RootPresentationRecognition

open Theory.PSL2.SemilinearCoverage
private theorem linear_matrix_gauss {F : Type*} [Field F] [CharP F 2] (a : Fˣ) :
    weyl F * (weyl F * uni (a : F) * (weyl F)⁻¹) =
      (weyl F * uni (↑a⁻¹ : F) * (weyl F)⁻¹) * tor a * uni (↑a⁻¹ : F) := by
  rw [inv_eq_of_mul_eq_one_right weyl_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem synchronizedLinear_gauss (a : (CoefficientField m)ˣ) :
    ((c.reflections 0).val : X ⧸ Q.D) *
      (((c.reflections 0).val : X ⧸ Q.D) *
        (synchronizedLinearChart Q split c (.ofAdd (a : CoefficientField m)) : X ⧸ Q.D) *
          ((c.reflections 0).val : X ⧸ Q.D)⁻¹) =
      (((c.reflections 0).val : X ⧸ Q.D) *
        (synchronizedLinearChart Q split c (.ofAdd (↑a⁻¹ : CoefficientField m)) : X ⧸ Q.D) *
          ((c.reflections 0).val : X ⧸ Q.D)⁻¹) *
        synchronizedLinearTorus Q split c a *
          (synchronizedLinearChart Q split c (.ofAdd (↑a⁻¹ : CoefficientField m)) : X ⧸ Q.D) := by
  let f : SL2 (CoefficientField m) →* X ⧸ Q.D :=
    (rankOne Q split 0).subtype.comp
      (linearPinning Q split (pinnedInput Q split c)).toMonoidHom
  let b := Units.map (synchronizedField Q split c).toMonoidHom a
  have h := congrArg f (linear_matrix_gauss b)
  simp only [map_mul, map_inv] at h
  have hw : f (weyl (CoefficientField m)) = ((c.reflections 0).val : X ⧸ Q.D) :=
    linearPinning_weyl Q split (pinnedInput Q split c)
  have hu (t : CoefficientField m) : f (uni (synchronizedField Q split c t)) =
      (synchronizedLinearChart Q split c (.ofAdd t) : X ⧸ Q.D) := rfl
  have hb : (b : CoefficientField m) = synchronizedField Q split c a := rfl
  have hbi : (↑b⁻¹ : CoefficientField m) = synchronizedField Q split c (↑a⁻¹ : CoefficientField m) := by
    simp [b]
  have ht : f (tor b) = synchronizedLinearTorus Q split c a := rfl
  rw [hw,hb,hbi,hu,hu,ht] at h
  exact h

private theorem synchronizedSourceLinear_chart_zero
    (d : SourcePositive.Charts Q split m)
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a)
    (x : CoefficientField m) :
    (d.chart (.inl 0) x : X ⧸ Q.D) =
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D) := by
  rw [hd]
  rw [synchronizedPositivePoint_pair_word]
  simp [positiveWord]

theorem synchronizedSourceLinear_gauss
    (d : SourcePositive.Charts Q split m)
    (T : SourceBorel.TorusData Q split d)
    (W : SourceNormalizer.WeylData Q split d T)
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a)
    (hW : ∀ s, W.n s = sourceSimpleReflection Q split c s)
    (hT : ∀ a : (CoefficientField m)ˣ,
      T.h (linearTau a) = synchronizedLinearTorus Q split c a)
    (a : (CoefficientField m)ˣ) :
    (W.n false : X ⧸ Q.D) * SourceSigned.pair Q split d T W (false,0) (a : (CoefficientField m)ˣ) =
      SourceSigned.pair Q split d T W (false,0) (↑a⁻¹ : (CoefficientField m)ˣ) *
        T.h (linearTau a) *
          SourceSigned.pair Q split d T W (true,0) (↑a⁻¹ : (CoefficientField m)ˣ) := by
  let R : SourceSigned.Equations Q split d T W :=
    synchronizedSourceSigned_equations Q split c d T W hd hW
  have hs := synchronizedLinear_gauss Q split c a
  rw [SourceSigned.pair_negative_simple Q split d T W R,
    SourceSigned.pair_negative_simple Q split d T W R,
    SourceSigned.pair_positive, hT]
  rw [synchronizedSourceLinear_chart_zero Q split c d hd (a : CoefficientField m)]
  rw [synchronizedSourceLinear_chart_zero Q split c d hd (↑a⁻¹ : CoefficientField m)]
  rw [hW]
  simpa [sourceSimpleReflection] using hs
private theorem synchronizedSourceSuzuki_chart_zero
    (d : SourcePositive.Charts Q split m)
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a)
    (x y : CoefficientField m) :
    (d.chart (.inr 0) (x,y) : X ⧸ Q.D) =
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) := by
  rw [hd]
  rw [synchronizedPositivePoint_quartet_word]
  simp [positiveWord]

theorem synchronizedSourceSuzuki_gauss
    (d : SourcePositive.Charts Q split m)
    (T : SourceBorel.TorusData Q split d)
    (W : SourceNormalizer.WeylData Q split d T)
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a)
    (hW : ∀ s, W.n s = sourceSimpleReflection Q split c s)
    (hT : ∀ a : (CoefficientField m)ˣ,
      T.h (suzukiTau a) =
        synchronizedSuzukiTorus Q split c (synchronizedSuzukiGaussParameter a))
    (a b : CoefficientField m) (hn : norm a b ≠ 0) :
    (W.n true : X ⧸ Q.D) * SourceSigned.quartet Q split d T W (false,0) a b =
      SourceSigned.quartet Q split d T W (false,0)
          (negativeFirst a b) (negativeSecond a b) *
        T.h (suzukiTau (Units.mk0 (norm a b) hn)) *
          SourceSigned.quartet Q split d T W (true,0)
            (positiveFirst a b) (positiveSecond a b) := by
  let R : SourceSigned.Equations Q split d T W :=
    synchronizedSourceSigned_equations Q split c d T W hd hW
  have hs := synchronizedSuzuki_gauss Q split c a b hn
  rw [SourceSigned.quartet_negative_simple Q split d T W R,
    SourceSigned.quartet_negative_simple Q split d T W R,
    SourceSigned.quartet_positive, hT]
  rw [synchronizedSourceSuzuki_chart_zero Q split c d hd,
    synchronizedSourceSuzuki_chart_zero Q split c d hd,
    synchronizedSourceSuzuki_chart_zero Q split c d hd]
  rw [hW]
  simpa [sourceSimpleReflection] using hs
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
