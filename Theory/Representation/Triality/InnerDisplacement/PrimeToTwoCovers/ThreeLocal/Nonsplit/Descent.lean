module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit.Raw
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Lang

/-!
# Simultaneous rational descent of the nonsplit triality torus

The cube of the folded Coxeter word exchanges the two hyperbolic halves of
Spin's faithful natural representation. It therefore inverts the actual
simple-coroot torus and commutes with the central reflection. The graph-field
map inverts the norm-one scalar torus and fixes all three prescribed Weyl
words. A single solution of the concrete Spin Lang equation consequently
conjugates the torus and these words into the graph-field fixed group.

The proved Geck--Spin comparison identifies that fixed group with the literal
`Standard.BinaryCarrier`: the fixed group is two-generated and the elementary
central kernel is trivial. Transport through this actual isomorphism constructs
`RationalRealization` without extra hypotheses, for every positive exponent,
including n = 1. This module imports `Raw` directly so that the three-primary
assembly can consume the result without an import cycle.

Sources: GLS3, Theorem 2.1.1 and Remark 2.1.7 (Lang and rational tori),
Theorem 2.2.6 and §§2.3--2.4 (elementary groups and central quotients),
`refs/KGroup/GLS3/chapter2.tex`; Steinberg 10.7--10.8,
`refs/KGroup/GLS3/Chapter2St2.tex`. The ultimate application is GLS3 §6.1.
-/

public section

open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.PointGeneration
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
noncomputable section

private theorem inverter_apply (z : QuadraticSpace Scalars) :
    (naturalAction Scalars inverterWord).1 z = (z.2, z.1) := by
  simp only [inverterWord, pow_succ, pow_zero, one_mul, coxeter, map_mul,
    Subgroup.coe_mul, LinearEquiv.mul_apply, simpleNormalizer_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem inverter_sq : inverterWord * inverterWord = 1 := by
  apply naturalAction_injective Scalars
  rw [map_mul, map_one]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, inverter_apply]
  rfl

private theorem inverter_inv : inverterWord⁻¹ = inverterWord :=
  inv_eq_of_mul_eq_one_left inverter_sq

private theorem inverter_reflection_commute : Commute inverterWord reflectionWord := by
  apply naturalAction_injective Scalars
  simp only [map_mul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, reflectionWord,
    simpleNormalizer_apply, inverter_apply]
  rfl

private theorem inverter_parameter (t : Fin 4 → Scalarsˣ) :
    inverterWord * CorootTorus.parameter Scalars t * inverterWord⁻¹ =
      (CorootTorus.parameter Scalars t)⁻¹ := by
  have hi : (CorootTorus.parameter Scalars t)⁻¹ =
      CorootTorus.parameter Scalars t⁻¹ := (map_inv (CorootTorus.pointHom Scalars) t).symm
  rw [hi, inverter_inv]
  apply naturalAction_injective Scalars
  simp only [map_mul, CorootTorus.naturalAction_parameter]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, inverter_apply,
    diagonalAction_spec]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [diagonalAction, CorootTorus.diagonal, mul_comm, mul_assoc]

private theorem sigma_simple (n : ℕ) (i : Fin 4) :
    GraphField.sigma Scalars n (simpleNormalizer Scalars i) =
      simpleNormalizer Scalars (typeD4DiagramPermutation i) := by
  have hd : Diagram.pinnedAut Scalars (simpleNormalizer Scalars i) =
      simpleNormalizer Scalars (typeD4DiagramPermutation i) :=
    (Diagram.pinnedAut_isPinned Scalars).simpleNormalizer Scalars i 1
  rw [GraphField.sigma_apply, hd, GraphField.frobenius_normalizerWord, one_pow]

private theorem sigma_coxeter (n : ℕ) : GraphField.sigma Scalars n coxeter = coxeter := by
  simp only [coxeter, map_mul, sigma_simple]
  apply naturalAction_injective Scalars
  simp only [map_mul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, simpleNormalizer_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem sigma_reflection (n : ℕ) :
    GraphField.sigma Scalars n reflectionWord = reflectionWord := sigma_simple n 1

private theorem sigma_cycle (n : ℕ) :
    GraphField.sigma Scalars n cycleWord = cycleWord := by
  simp only [cycleWord, map_pow, sigma_coxeter]

private theorem sigma_inverter (n : ℕ) :
    GraphField.sigma Scalars n inverterWord = inverterWord := by
  simp only [inverterWord, map_pow, sigma_coxeter]

private theorem sigma_rawTorus (n : ℕ) (a : Coordinates n) :
    GraphField.sigma Scalars n (rawTorus n a) = (rawTorus n a)⁻¹ := by
  change GraphField.sigma Scalars n (CorootTorus.parameter Scalars (expand n a)) = _
  have hd : Diagram.pinnedAut Scalars (CorootTorus.parameter Scalars (expand n a)) =
      CorootTorus.parameter Scalars (Diagram.permutedParameters Scalars (expand n a)) :=
    (Diagram.pinnedAut_isPinned Scalars).parameter Scalars (expand n a)
  rw [GraphField.sigma_apply, hd, GraphField.frobenius_parameter]
  have ht : (fun i => Diagram.permutedParameters Scalars (expand n a) i ^ (2 ^ n)) =
      (expand n a)⁻¹ := by
    apply inv_injective
    rw [inv_inv]
    calc
      _ = signedTwist n (expand n a) := by
        funext i
        fin_cases i <;> rfl
      _ = expand n a := signedTwist_expand n a
  rw [ht]
  exact map_inv (CorootTorus.pointHom Scalars) (expand n a)

private theorem twisted_rawTorus (n : ℕ) (a : Coordinates n) :
    inverterWord * GraphField.sigma Scalars n (rawTorus n a) * inverterWord⁻¹ =
      rawTorus n a := by
  rw [sigma_rawTorus]
  change (MulAut.conj inverterWord) ((rawTorus n a)⁻¹) = _
  rw [map_inv]
  change (inverterWord * CorootTorus.parameter Scalars (expand n a) * inverterWord⁻¹)⁻¹ = _
  rw [inverter_parameter, inv_inv]
  rfl

private theorem conjugate_fixed (n : ℕ) {u g : Ambient}
    (hu : u * (GraphField.sigma Scalars n u)⁻¹ = inverterWord)
    (hg : inverterWord * GraphField.sigma Scalars n g * inverterWord⁻¹ = g) :
    GraphField.sigma Scalars n (u⁻¹ * g * u) = u⁻¹ * g * u := by
  have hfu : GraphField.sigma Scalars n u = inverterWord⁻¹ * u := by
    rw [← hu]
    group
  rw [map_mul, map_mul, map_inv, hfu]
  calc
    _ = u⁻¹ * (inverterWord * GraphField.sigma Scalars n g * inverterWord⁻¹) * u := by group
    _ = _ := by rw [hg]

private def spinFixedEquiv (n : ℕ) (hn : 0 < n) :
    Standard.BinaryCarrier n hn ≃* GraphField.FixedGroup Scalars n :=
  (Standard.ConcreteBruhat.FixedDescent.carrierFixedEquiv
    (Standard.binaryParameters n hn) rfl).trans (Standard.binarySpinFixedEquiv Scalars n hn)

/-- One conjugator simultaneously realizes the norm-one torus, central reflection,
Coxeter square and Coxeter cube in the genuine finite triality carrier. -/
theorem rationalRealization_nonempty (n : ℕ) (hn : 0 < n) :
    Nonempty (RationalRealization n hn) := by
  obtain ⟨u, hu⟩ := CyclotomicTori.PhiTwelve.graphField_lang_surjective Scalars n hn inverterWord
  let e := spinFixedEquiv n hn
  let f : Standard.BinaryCarrier n hn →* Ambient :=
    (GraphField.fixedSubgroup Scalars n).subtype.comp e.toMonoidHom
  let t : Coordinates n →* GraphField.FixedGroup Scalars n :=
    ((MulAut.conj u⁻¹).toMonoidHom.comp (rawTorus n)).codRestrict
      (GraphField.fixedSubgroup Scalars n) (fun a => by
        change GraphField.sigma Scalars n (u⁻¹ * rawTorus n a * (u⁻¹)⁻¹) =
          u⁻¹ * rawTorus n a * (u⁻¹)⁻¹
        simpa only [inv_inv] using conjugate_fixed n hu (twisted_rawTorus n a))
  have hr : inverterWord * GraphField.sigma Scalars n reflectionWord * inverterWord⁻¹ =
      reflectionWord := by
    rw [sigma_reflection, inverter_reflection_commute.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hc : inverterWord * GraphField.sigma Scalars n cycleWord * inverterWord⁻¹ =
      cycleWord := by
    have hcomm : Commute inverterWord cycleWord := (Commute.refl coxeter).pow_pow 3 2
    rw [sigma_cycle, hcomm.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hi : inverterWord * GraphField.sigma Scalars n inverterWord * inverterWord⁻¹ =
      inverterWord := by rw [sigma_inverter]; group
  let r : GraphField.FixedGroup Scalars n :=
    ⟨u⁻¹ * reflectionWord * u, conjugate_fixed n hu hr⟩
  let c : GraphField.FixedGroup Scalars n :=
    ⟨u⁻¹ * cycleWord * u, conjugate_fixed n hu hc⟩
  let w : GraphField.FixedGroup Scalars n :=
    ⟨u⁻¹ * inverterWord * u, conjugate_fixed n hu hi⟩
  refine ⟨{
    embedding := f
    embedding_injective := Subtype.val_injective.comp e.injective
    conjugator := u
    torus := e.symm.toMonoidHom.comp t
    torus_eq := ?_
    reflection := e.symm r
    cycle := e.symm c
    inverter := e.symm w
    reflection_eq := ?_
    cycle_eq := ?_
    inverter_eq := ?_ }⟩
  · intro a
    change (e (e.symm (t a))).val = _
    rw [e.apply_symm_apply]
    change u⁻¹ * rawTorus n a * (u⁻¹)⁻¹ = _
    rw [inv_inv]
  · exact congrArg Subtype.val (e.apply_symm_apply r)
  · exact congrArg Subtype.val (e.apply_symm_apply c)
  · exact congrArg Subtype.val (e.apply_symm_apply w)

end
end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
