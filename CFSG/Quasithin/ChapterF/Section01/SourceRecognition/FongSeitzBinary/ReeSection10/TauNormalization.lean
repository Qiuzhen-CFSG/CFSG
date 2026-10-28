module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.GaussEquations
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusSimpleActions

/-!
# The native Gauss torus parameters in synchronized source coordinates

Both native tau elements are products of two simple coroot words. Comparing
those words with the actual diagonal torus and reading its two long-root
characters gives the exact linear and Suzuki parameters. The proved
coordinate change then identifies their normalized synchronized source
images. These identities discharge both Gauss torus premises in the literal
source quotient, including the full binary endpoint.

Source: GLS3 2.3.4--8 and Table 2.4; Fong--Seitz II (1974), §10,
(10.10)--(10.12). All torus words use the existing inverse-diagonal convention.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open RootPresentationRecognition Parabolics
open LocalBlockInput.PairRigidity.BlockParameters
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open ConverseParabolics.FullLeviRepresentation
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
variable {m : ℕ}

private theorem tau_eq_of_matrix (t : RootPresentationRecognition.TorusParameter m)
    (u : TorusParameters m)
    (h : (toSplitGroup m (RootPresentationRecognition.torus m t)).val = (torusMatrix u)⁻¹) :
    t = (rootScale u (typeF4SimpleRootIndex 0), rootScale u (typeF4SimpleRootIndex 1)) := by
  change (toSplitGroup m (torusElement t.1 t.2)).val = _ at h
  rw [torusElement_matrix] at h
  have he := torusMatrix_injective (inv_injective h)
  apply Prod.ext
  · simpa only [blockTorus_simple, Matrix.cons_val_zero] using
      congrArg (fun v => rootScale v (typeF4SimpleRootIndex 0)) he
  · simpa only [blockTorus_simple, Matrix.cons_val_one, Matrix.cons_val_zero] using
      congrArg (fun v => rootScale v (typeF4SimpleRootIndex 1)) he

private def corootPair (i j : Fin 4) (a b : (CoefficientField m)ˣ) : TorusParameters m :=
  integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) a *
    integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv j) b

private theorem corootPair_matrix (i j : Fin 4) (a b : (CoefficientField m)ˣ) :
    (torusWord m (typeF4SimpleRootIndex i) a *
      torusWord m (typeF4SimpleRootIndex j) b).val =
        (torusMatrix (corootPair i j a b))⁻¹ := by
  simp only [Subgroup.coe_mul, ← typeF4RootPairing_baseEquiv_val, torusWord_simple_coe]
  have hinv (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :
      integralChevalleySimpleCorootParameter i u⁻¹ =
        (integralChevalleySimpleCorootParameter i u)⁻¹ := by
    funext q
    simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
    split_ifs <;> simp
  rw [hinv, hinv, ← map_mul, ← mul_inv]
  change diagonalTorusHom m (corootPair i j a b)⁻¹ = _
  rw [map_inv]
  rfl

private theorem corootPair_scale (i j k : Fin 4) (a b : (CoefficientField m)ˣ) :
    rootScale (corootPair i j a b) (typeF4SimpleRootIndex k) =
      a ^ typeF4CartanMatrix k i * b ^ typeF4CartanMatrix k j := by
  have hp (r s : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex r) (typeF4SimpleRootIndex s) = typeF4CartanMatrix r s :=
    typeF4RootPairing_base_cartan_apply r s
  unfold corootPair
  rw [rootScale_mul]
  simp only [rootScale,
    integralChevalleyRootScale_simpleCorootParameter, typeF4RootPairing_baseEquiv_val, hp]

theorem linearTau_characters (a : (CoefficientField m)ˣ) :
    linearTau a = (a^2, a⁻¹) := by
  have ht := tau_eq_of_matrix (linearTau a)
    (corootPair 0 3 a (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0)).toMonoidHom a))
    (by rw [torus_linearTau, linearWeyl_ratio_split]; exact corootPair_matrix ..)
  rw [corootPair_scale, corootPair_scale] at ht
  simpa [typeF4CartanMatrix, Fin.ext_iff] using ht

theorem suzukiTau_characters (a : (CoefficientField m)ˣ) :
    suzukiTau a = ((Units.map (titsEnd m).toMonoidHom a)⁻¹,
      (Units.map (titsEnd m).toMonoidHom a)^2 / a^2) := by
  have ht := tau_eq_of_matrix (suzukiTau a)
    (corootPair 1 2 (Units.map (titsEnd m).toMonoidHom a) a)
    (by rw [torus_suzukiTau]; exact corootPair_matrix ..)
  rw [corootPair_scale, corootPair_scale] at ht
  simpa [typeF4CartanMatrix, Fin.ext_iff, div_eq_mul_inv, inv_pow] using ht


theorem linearTau_eq_torusCharacters (a : (CoefficientField m)ˣ) :
    linearTau a = torusCharacters (a,1) := by
  rw [linearTau_characters]
  simp [torusCharacters]

private theorem suzukiGaussParameter_outer (a : (CoefficientField m)ˣ) :
    synchronizedSuzukiGaussParameter a ^ (1+2^m) =
      (Units.map (titsEnd m).toMonoidHom a)⁻¹ := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, synchronizedSuzukiGaussParameter_coe,
    Units.val_inv_eq_inv_val, Units.coe_map]
  change (((a : CoefficientField m) / titsEnd m a)^2)^(1+2^m) = (titsEnd m a)⁻¹
  have hmid : (((a : CoefficientField m) / titsEnd m a)^2)^(2^m) =
      titsEnd m a / (a : CoefficientField m)^2 := by
    rw [←show ∀ z : CoefficientField m, theta m z = z^(2^m) from fun _ => rfl]
    rw [map_pow,map_div₀,theta_tits,div_pow,theta_sq]
  rw [pow_add,pow_one,hmid]
  field_simp

theorem suzukiTau_eq_torusCharacters (a : (CoefficientField m)ˣ) :
    suzukiTau a = torusCharacters (1,synchronizedSuzukiGaussParameter a) := by
  rw [suzukiTau_characters]
  apply Prod.ext
  · simpa only [torusCharacters, MonoidHom.coe_mk, OneHom.coe_mk,
      one_pow, one_mul] using (suzukiGaussParameter_outer a).symm
  · change (Units.map (titsEnd m).toMonoidHom a)^2 / a^2 =
      (1*synchronizedSuzukiGaussParameter a)⁻¹
    rw [one_mul]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, Units.coe_map]
    change (titsEnd m (a : CoefficientField m))^2 / (a : CoefficientField m)^2 =
      ((synchronizedSuzukiGaussParameter a)⁻¹ : CoefficientField m)
    rw [synchronizedSuzukiGaussParameter_inv_coe, div_pow]

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n : ℕ}
  (c : ReeSixHData Q split n m)

theorem normalizedSynchronizedTorus_linearTau (a : (CoefficientField m)ˣ) :
    normalizedSynchronizedTorus Q split c (linearTau a) =
      synchronizedLinearTorus Q split c a := by
  rw [linearTau_eq_torusCharacters, normalizedSynchronizedTorus_characters, map_one, mul_one]

theorem normalizedSynchronizedTorus_suzukiTau (a : (CoefficientField m)ˣ) :
    normalizedSynchronizedTorus Q split c (suzukiTau a) =
      synchronizedSuzukiTorus Q split c (synchronizedSuzukiGaussParameter a) := by
  rw [suzukiTau_eq_torusCharacters, normalizedSynchronizedTorus_characters, map_one, one_mul]

/-- Both literal Gauss equations follow from the synchronized charts and
reflections whenever the full torus map is the constructed normalized torus. -/
theorem normalizedSynchronizedSourceGauss
    (d : SourcePositive.Charts Q split m)
    (T : SourceBorel.TorusData Q split d)
    (W : SourceNormalizer.WeylData Q split d T)
    (hd : ∀ i a, (d.chart i a : X ⧸ Q.D) = synchronizedPositivePoint Q split c i a)
    (hW : ∀ s, W.n s = sourceSimpleReflection Q split c s)
    (hT : T.h = normalizedSynchronizedTorus Q split c) :
    Global.SourceGauss Q split d T W where
  linear := synchronizedSourceLinear_gauss Q split c d T W hd hW
    (by intro a; rw [hT]; exact normalizedSynchronizedTorus_linearTau Q split c a)
  suzuki := synchronizedSourceSuzuki_gauss Q split c d T W hd hW
    (by intro a; rw [hT]; exact normalizedSynchronizedTorus_suzukiTau Q split c a)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
