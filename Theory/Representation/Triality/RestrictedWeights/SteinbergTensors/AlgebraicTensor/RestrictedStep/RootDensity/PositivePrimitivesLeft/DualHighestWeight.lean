module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.Duality
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.WeightNilpotence

/-!
# The rational dual highest weight from opposition

Take a genuine Borel highest vector `f` in the actual rational dual. After
precomposing `f` with the action of the supplied opposition point, every
negative root group fixes this functional. Polynomial coefficient comparison
therefore makes it vanish on every nonempty negative root-operator word.
Negative cyclicity forces its value on the original highest vector to be
nonzero. The torus-inversion equation then identifies the two highest weights.

The whole Borel condition comes from `highWeight_exists_of_borel`; annihilation
by first coefficients is used only to prove the nonzero pairing. Opposition
remains an explicit geometric input. Field and carrier universes are independent,
and the original positive Borel and left-weight embedding are retained.

Source: the contragredient highest-weight formula `-w₀λ` in Steinberg,
*Lectures on Chevalley Groups*, Lemma 73 (the local transcription is
`refs/KGroup/GLS3/Chapter2St1.tex`, pp. 215–216). The negative cyclicity argument
is the primitive-vector argument of Steinberg, *Representations of Algebraic
Groups* (1963), §§2, 4 and 11.1, used for GLS3 Theorem 2.8.5 and
Corollary 2.8.6(a).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Negative cyclicity detects a nonzero dual highest vector after opposition. -/
private theorem dual_highest_opposition_pairing_ne_zero (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (O : Opposition S) {ν : TorusWeight S.torus} {f : Module.Dual k V}
    (hf : HasHighWeight (dualRepresentation ρ hρ) S.borel S.torus f ν)
    {v : V} (hspan : negativeRootSpan S ρ hρ v = ⊤) :
    f ((ρ.action O.point).val v) ≠ 0 := by
  let N : Module.End k V := (ρ.action O.point).val
  let F : Module.Dual k V := f.comp N
  have hfix (r : PositiveRoot S) (t : k) (y : V) :
      F ((ρ.action (S.chevalley.x (S.roots.neg r.val) t)).val y) = F y := by
    have hcomm := congrArg (fun g => (ρ.action g).val y) (O.root_commute r.val t)
    simp only [map_mul, Units.val_mul, Module.End.mul_apply] at hcomm
    change f (N ((ρ.action (S.chevalley.x (S.roots.neg r.val) t)).val y)) = f (N y)
    rw [← hcomm]
    have hd := dualRepresentation_spec ρ hρ (S.chevalley.x r.val t) f (N y)
    rw [positive_root_fixed_of_highWeight S _ (dualRepresentation_rational ρ hρ)
      hf r.val r.property t, rootElement_inv] at hd
    exact hd.symm
  have hkill (r : PositiveRoot S) (y : V) :
      F (rootOperator S ρ hρ (S.roots.neg r.val) y) = 0 := by
    have hp : curvePolynomial ρ hρ (rootMorphism S (S.roots.neg r.val)) F y =
        Polynomial.C (F y) := by
      apply Polynomial.funext
      intro t
      rw [curvePolynomial_eval, rootMorphism_apply, hfix, Polynomial.eval_C]
    change F (curveOperator ρ hρ (rootMorphism S (S.roots.neg r.val)) y) = 0
    rw [dual_curveOperator, hp]
    simp
  intro hzero
  have hF : F = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    change F ((l.map fun r => rootOperator S ρ hρ (S.roots.neg r.val)).prod v) = 0
    cases l with
    | nil => exact hzero
    | cons r l =>
      simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply] using
        hkill r ((l.map fun r => rootOperator S ρ hρ (S.roots.neg r.val)).prod v)
  apply hf.1.1
  ext x
  obtain ⟨y, rfl⟩ := (ρ.action O.point).toLinearEquiv.surjective x
  exact congrArg (fun q : Module.Dual k V => q y) hF

/-- Opposition turns the inverse weight from duality back into the original weight. -/
private theorem dual_highest_weight_eq_of_negative_span (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (O : Opposition S) {χ ν : TorusWeight S.torus} {v : V} {f : Module.Dual k V}
    (hv : HasHighWeight ρ S.borel S.torus v χ)
    (hf : HasHighWeight (dualRepresentation ρ hρ) S.borel S.torus f ν)
    (hspan : negativeRootSpan S ρ hρ v = ⊤) : ν = χ := by
  have hpair := dual_highest_opposition_pairing_ne_zero S ρ hρ O hf hspan
  apply TorusCharacter.pointCharacter_injective
  ext t
  have hcomm := congrArg (fun g => (ρ.action g).val v) (O.torus_commute t⁻¹)
  simp only [map_mul, Units.val_mul, Module.End.mul_apply, inv_inv] at hcomm
  rw [hv.2.2, map_smul] at hcomm
  have hd := dualRepresentation_spec ρ hρ (S.torus.includePoint t) f
    ((ρ.action O.point).val v)
  rw [hf.2.2] at hd
  have hinv : (S.torus.includePoint t)⁻¹ = S.torus.includePoint t⁻¹ := rfl
  rw [hinv, hcomm, map_smul] at hd
  apply mul_right_cancel₀ hpair
  exact hd

/-- With genuine opposition supplied, the actual rational dual has the same
left basic highest weight as the negative-cyclic original representation. -/
theorem dualRepresentation_hasHighWeight_of_left_basic_negative_span
    (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsIrreducibleRepresentation ρ) {a : BasicWeight}
    (_ha : a ≠ fun _ => false) {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (hspan : negativeRootSpan S ρ hρ.1 v = ⊤) (O : Opposition S) :
    ∃ f, HasHighWeight (dualRepresentation ρ hρ.1) S.borel S.torus f
      (S.leftWeightEmbedding (coefficient a)) := by
  let : Nontrivial V := ⟨⟨v, 0, hv.1.1⟩⟩
  obtain ⟨f, ν, hf⟩ := highWeight_exists_of_borel S.borel S.torus
    (dualRepresentation ρ hρ.1) (dualRepresentation_rational ρ hρ.1)
    S.bigCell.data.positive_witness.borel S.maximalTorus S.bigCell.torus_le_positive
  have hν := dual_highest_weight_eq_of_negative_span S ρ hρ.1 O hv hf hspan
  exact ⟨f, hν ▸ hf⟩

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft
