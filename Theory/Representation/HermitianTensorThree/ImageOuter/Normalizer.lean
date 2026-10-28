module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Contracts
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.PGL
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Centralizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.InducedAction

/-!
# Assembly of the Hermitian tensor normalizer

The literal binary normalizer consists exactly of the semilinear GL₃
congruences. The forward inclusion combines the proved scalar-centralizer
theorem and coverage of the induced automorphisms. After removing a standard
induced action, the residual map is a fixed-field scalar; its square root
absorbs that scalar into the GL₃ matrix. Every such congruence normalizes
the binary SL₃ image, proving the converse.

The source-overgroup application uses relative normality of the actual
solvable residual via `sourceOvergroup_le_normalizer`. The PGL₃(4)
identification retains the given PSL₃ image. This extension requires the
full GL₃ factor: at n = 1, fixed-field scalars are trivial and cannot supply
the inner-diagonal extension in H.4.6(3).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, standing
hypotheses on p.377, H.4.2 setup on p.380, and H.4.6(3) on p.382.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

private theorem commutes_of_conj_eq {G : Type*} [Group G] (e s a : G)
    (h : e * a * e⁻¹ = s * a * s⁻¹) :
    (s⁻¹ * e) * a = a * (s⁻¹ * e) := by
  have h' := congrArg (fun x => s⁻¹ * x * e) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h'

private theorem eq_mul_of_inv_mul_eq {G : Type*} [Group G] (e s c : G)
    (h : s⁻¹ * e = c) : e = s * c := by
  rw [← h, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Removing the known induced action leaves a scalar, which can be absorbed into GL₃. -/
theorem normalizerCoverage_of_scalarCentralizer_of_inducedAction
    (hcentral : ScalarCentralizerCoverage n) (hinduced : InducedActionCoverage n) :
    NormalizerCoverage n := by
  intro e he
  obtain ⟨g, τ, haction⟩ := hinduced e he
  let s := semilinearCongruence n g τ
  have hcomm (a : Cover n) :
      (s⁻¹ * e) * binaryActionHom n a = binaryActionHom n a * (s⁻¹ * e) :=
    commutes_of_conj_eq e s (binaryActionHom n a) (haction a)
  obtain ⟨c, hc⟩ := hcentral (s⁻¹ * e) hcomm
  obtain ⟨d, hd⟩ := fixedScalar_eq_congruence n c
  have heq : e = s * binaryCongruence n (Matrix.GeneralLinearGroup.scalar (Fin 3) d) :=
    eq_mul_of_inv_mul_eq e s _ (hc.trans hd)
  let gd := Matrix.GeneralLinearGroup.scalar (Fin 3) d
  let gdτ := Matrix.GeneralLinearGroup.map τ.toRingHom gd
  refine ⟨g * gdτ, τ, ?_⟩
  intro X
  rw [heq]
  change g.val * (gd.val * X.val * adjoint n gd.val).map τ * adjoint n g.val =
    (g * gdτ).val * X.val.map τ * adjoint n (g * gdτ).val
  rw [Matrix.map_mul, Matrix.map_mul, ← adjoint_map]
  change g.val * (gdτ.val * X.val.map τ * adjoint n gdτ.val) * adjoint n g.val =
    (g.val * gdτ.val) * X.val.map τ * adjoint n (g.val * gdτ.val)
  rw [adjoint_mul]; simp only [Matrix.mul_assoc]

/-- Exact membership, with the two forward-coverage inputs kept explicit. -/
theorem mem_binaryNormalizer_iff_of_scalarCentralizer_of_inducedAction
    (hcentral : ScalarCentralizerCoverage n) (hinduced : InducedActionCoverage n)
    (e : Space n ≃ₗ[ZMod 2] Space n) :
    e ∈ binaryNormalizer n ↔ HasCongruenceExpression n e :=
  ⟨normalizerCoverage_of_scalarCentralizer_of_inducedAction n hcentral hinduced e,
    mem_normalizer_of_hasCongruenceExpression n e⟩

/-- Application to the literal source residual convention L = M∞. -/
theorem sourceOvergroup_hasCongruenceExpression_of_scalarCentralizer_of_inducedAction
    (hcentral : ScalarCentralizerCoverage n) (hinduced : InducedActionCoverage n)
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (e : Space n ≃ₗ[ZMod 2] Space n) (he : e ∈ M) : HasCongruenceExpression n e :=
  normalizerCoverage_of_scalarCentralizer_of_inducedAction n hcentral hinduced e
    (sourceOvergroup_le_normalizer n M hM he)

/-- Every binary normalizer element is an actual semilinear GL₃ congruence. -/
theorem normalizerCoverage : NormalizerCoverage n :=
  normalizerCoverage_of_scalarCentralizer_of_inducedAction n
    (scalarCentralizerCoverage n)
    (inducedActionCoverage_of_scalarCentralizer n (scalarCentralizerCoverage n))

/-- Exact description of the literal binary normalizer, including inner-diagonal actions. -/
theorem mem_binaryNormalizer_iff (e : Space n ≃ₗ[ZMod 2] Space n) :
    e ∈ binaryNormalizer n ↔ HasCongruenceExpression n e :=
  ⟨normalizerCoverage n e, mem_normalizer_of_hasCongruenceExpression n e⟩

/-- The source assumption L = M∞ puts every element of M in the computed normalizer. -/
theorem sourceOvergroup_hasCongruenceExpression
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (e : Space n ≃ₗ[ZMod 2] Space n) (he : e ∈ M) : HasCongruenceExpression n e :=
  normalizerCoverage n e (sourceOvergroup_le_normalizer n M hM he)

end Representation.HermitianTensorThree.ImageOuter
