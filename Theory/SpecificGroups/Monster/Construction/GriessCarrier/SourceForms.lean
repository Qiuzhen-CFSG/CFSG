module
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.ShortCubic
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.Duality
public import Theory.SpecificGroups.Monster.Construction.LocalC.OrthogonalSpace
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinQuotient

/-!
# The exact Griess forms for an explicit source lattice comparison

On the existing LocalC orthogonal sum, the symmetric block, actual short-lift
cubic block, and three mixed blocks give the five source terms. The spin factor
is the descended representation of the concrete extraspecial image in `N/K`.
Its orthogonal involutions are self-adjoint and its center acts as minus identity,
so the signed mixed block descends and is symmetric with no action premises.

All ten homogeneous cases are proved: five prescribed blocks and five zeros.
Each mixed block has its three unscaled placements. Positivity of the existing
orthogonal form recovers a commutative bilinear multiplication by duality, and
its isometric stabilizer equals the simultaneous stabilizer of the two forms.

The only remaining parameter is the Section 27 lattice comparison `e`. The
parameter-free carrier must instantiate it with the proved source coordinate
map. This module does not supply or assume that map's existence.

Source: Aschbacher, *Sporadic Groups*, (28.1)–(28.6) and Lemmas 28.7–28.12,
printed pp. 151–154. The real Leech normalization and sign-independent tensors
are reused from LocalC without replacing its spaces or representatives.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct Matrix
namespace Sporadic.Monster.Construction.Griess
open LocalC TrialitySpin TrialitySpin.SpinAction

variable (e : LatticeComparison)

/-- The actual descended spin operator attached to a short extraspecial lift. -/
def shortSpin (r : ShortLift e) : Module.End ℝ SpinSpace := imageRepresentation r.val

theorem shortSpin_sign (r : ShortLift e) :
    shortSpin e ((shortLiftSigns e).flip r) = -shortSpin e r := by
  apply representation_mul_sign imageRepresentation q1ImageCenterGenerator
  intro v
  rw [imageRepresentation_center]
  rfl

theorem shortSpin_involutive (r : ShortLift e) (v : SpinSpace) :
    shortSpin e r (shortSpin e r v) = v := by
  change (imageRepresentation r.val * imageRepresentation r.val) v = v
  rw [← map_mul, ← pow_two, shortLift_square, map_one]
  rfl

theorem shortSpin_isometry (r : ShortLift e) (v w : SpinSpace) :
    bothAxesDomain.form (shortSpin e r v) (shortSpin e r w) = bothAxesDomain.form v w :=
  imageRepresentation_isometry r.val v w

theorem shortSpin_self_adjoint (r : ShortLift e) (v w : SpinSpace) :
    bothAxesDomain.form (shortSpin e r v) w = bothAxesDomain.form v (shortSpin e r w) :=
  involution_self_adjoint _ _ (shortSpin_involutive e r) (shortSpin_isometry e r) v w

/-- The mixed `S,R,R` block of (28.2), with the source short tensor. -/
def sourceSRR : SymmetricPart →ₗ[ℝ] ShortSpace e →ₗ[ℝ] ShortSpace e →ₗ[ℝ] ℝ :=
  signedDiagonalBlock (shortLiftSigns e) (shortLiftTensor e)

/-- The mixed `S,W,W` block of (28.5), on the fixed natural-spin space. -/
def sourceSWW : SymmetricPart →ₗ[ℝ] MinusSpace →ₗ[ℝ] MinusSpace →ₗ[ℝ] ℝ :=
  symmetricTensorBlock bothAxesDomain.form

/-- The mixed `R,W,W` block of (28.6), using the actual descended spin action. -/
def sourceRWW : ShortSpace e →ₗ[ℝ] MinusSpace →ₗ[ℝ] MinusSpace →ₗ[ℝ] ℝ :=
  signedTensorBlock (shortLiftSigns e) bothAxesDomain.form (shortLiftTensor e) (shortSpin e)

theorem sourceSRR_vector (A : SymmetricPart) (r s : ShortLift e) :
    sourceSRR e A (shortVector e r) (shortVector e s) =
      symmetricGamma A (shortLiftTensor e r) * shortForm e (shortVector e r) (shortVector e s) :=
  signedDiagonalBlock_delta _ _ (shortLiftTensor_sign e) A r s

/-- Formula (28.2) in any genuine short representative's real coordinates. -/
theorem sourceSRR_representative (A : SymmetricPart) (r s : ShortLift e)
    (ξ : Atlas.Lattices.LeechShell 4) (hξ : shortReduction ξ = shortLiftClass e r) :
    sourceSRR e A (shortVector e r) (shortVector e s) =
      (∑ i, ∑ j, A.val i j * leechVector ξ.val i * leechVector ξ.val j) *
        shortForm e (shortVector e r) (shortVector e s) := by
  rw [sourceSRR_vector]
  have ht : shortLiftTensor e r = rankOne (leechVector ξ.val) := by
    rw [shortLiftTensor, ← hξ, shortTensor_eq]
  rw [ht, symmetricGamma_rankOne]

theorem sourceSRR_symmetric (A : SymmetricPart) (v w : ShortSpace e) :
    sourceSRR e A v w = sourceSRR e A w v :=
  signedDiagonalBlock_symmetric _ _ A v w

theorem sourceSWW_tmul (A : SymmetricPart) (a b : NaturalSpace) (v w : SpinSpace) :
    sourceSWW A (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) =
      ((a ᵥ* A.val) ⬝ᵥ b + Matrix.trace A.val * (a ⬝ᵥ b) / 8) * bothAxesDomain.form v w :=
  symmetricTensorBlock_tmul _ A a b v w

theorem sourceSWW_symmetric (A : SymmetricPart) (v w : MinusSpace) :
    sourceSWW A v w = sourceSWW A w v :=
  symmetricTensorBlock_symmetric _ bothAxesDomain.signedOrbits.form_symmetric A v w

/-- Signed descent of the actual mixed coefficient. -/
theorem sourceRWW_vector (r : ShortLift e) :
    sourceRWW e (shortVector e r) =
      shortTensorBlock bothAxesDomain.form (shortLiftTensor e r) (imageRepresentation r.val) :=
  signedTensorBlock_delta _ _ _ _ (shortLiftTensor_sign e) (shortSpin_sign e) r

theorem sourceRWW_symmetric (r : ShortSpace e) (v w : MinusSpace) :
    sourceRWW e r v w = sourceRWW e r w v :=
  signedTensorBlock_symmetric _ _ _ _ bothAxesDomain.signedOrbits.form_symmetric
    (shortSpin_involutive e) (shortSpin_isometry e) r v w

/-- Equation (28.6) for any actual short Leech representative of the lift.
The operator is exactly `I - 2 ξ ξᵀ`, with no rescaling of `ξ`. -/
theorem sourceRWW_representative (r : ShortLift e) (ξ : Atlas.Lattices.LeechShell 4)
    (hξ : shortReduction ξ = shortLiftClass e r)
    (a b : NaturalSpace) (v w : SpinSpace) :
    sourceRWW e (shortVector e r) (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) =
      (a ⬝ᵥ b - 2 * (a ⬝ᵥ leechVector ξ.val) * (leechVector ξ.val ⬝ᵥ b)) *
        bothAxesDomain.form (imageRepresentation r.val v) w / 8 := by
  rw [sourceRWW_vector]
  apply shortTensorBlock_rankOne
  have ht : shortLiftTensor e r = rankOne (leechVector ξ.val) := by
    rw [shortLiftTensor, ← hξ, shortTensor_eq]
  intro i j
  rw [ht]
  rfl

/-- The natural coefficient is the existing source correction (28.6). -/
theorem shortNaturalBlock_correction (r : ShortLift e) (a b : NaturalSpace) :
    shortNaturalBlock (shortLiftTensor e r) a b =
      naturalForm (shortLiftCorrection e r a) b := by
  rw [shortNaturalBlock_rankOne (shortLiftTensor e r)
    (leechVector (shortRepresentative (shortLiftClass e r)).val) a b (fun _ _ => rfl)]
  change a ⬝ᵥ b - 2 * (a ⬝ᵥ _) * (_ ⬝ᵥ b) =
    (a - (2 * (a ⬝ᵥ _)) • _) ⬝ᵥ b
  rw [sub_dotProduct, smul_dotProduct]
  rfl

/-- Formula (28.6) paired against any pure tensor, in the original source notation. -/
theorem sourceRWW_correction (r : ShortLift e) (a b : NaturalSpace) (v w : SpinSpace) :
    sourceRWW e (shortVector e r) (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) =
      naturalForm (shortLiftCorrection e r a) b *
        bothAxesDomain.form (imageRepresentation r.val v) w / 8 := by
  rw [sourceRWW_vector, shortTensorBlock_tmul, shortNaturalBlock_correction]

/-- The exact five-block Griess form on the source orthogonal sum.
Only the Section 27 lattice comparison remains an explicit parameter. -/
def sourceBeta : TrilinearForm (OrthogonalSpace e) :=
  fiveBlockForm symmetricBlock (shortCubic e) (sourceSRR e) sourceSWW (sourceRWW e)
    (symmetricProjection e) (shortProjection e) (minusProjection e)

theorem sourceBeta_swap_left (x y z : OrthogonalSpace e) :
    sourceBeta e x y z = sourceBeta e y x z :=
  fiveBlockForm_swap_left _ _ _ _ _ _ _ _ symmetricBeta_swap_left
    (shortCubic_swap_left e) (sourceSRR_symmetric e) sourceSWW_symmetric
    (sourceRWW_symmetric e) x y z

theorem sourceBeta_swap_right (x y z : OrthogonalSpace e) :
    sourceBeta e x y z = sourceBeta e x z y :=
  fiveBlockForm_swap_right _ _ _ _ _ _ _ _ symmetricBeta_swap_right
    (shortCubic_swap_right e) (sourceSRR_symmetric e) sourceSWW_symmetric
    (sourceRWW_symmetric e) x y z

theorem sourceBeta_permute (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → OrthogonalSpace e) :
    sourceBeta e (v (σ 0)) (v (σ 1)) (v (σ 2)) = sourceBeta e (v 0) (v 1) (v 2) :=
  permute_of_swap _ (sourceBeta_swap_left e) (sourceBeta_swap_right e) σ v

/-- The three placements of each mixed block occur once, without averaging. -/
theorem sourceBeta_components (x y z : OrthogonalSpace e) :
    sourceBeta e x y z =
      symmetricBlock x.2.2 y.2.2 z.2.2 + shortCubic e x.2.1 y.2.1 z.2.1 +
      (sourceSRR e x.2.2 y.2.1 z.2.1 + sourceSRR e y.2.2 x.2.1 z.2.1 +
        sourceSRR e z.2.2 x.2.1 y.2.1) +
      (sourceSWW x.2.2 y.1 z.1 + sourceSWW y.2.2 x.1 z.1 + sourceSWW z.2.2 x.1 y.1) +
      (sourceRWW e x.2.1 y.1 z.1 + sourceRWW e y.2.1 x.1 z.1 + sourceRWW e z.2.1 x.1 y.1) := rfl

theorem sourceBeta_SSS (A B C : SymmetricPart) :
    sourceBeta e (symmetricInclusion e A) (symmetricInclusion e B) (symmetricInclusion e C) =
      symmetricBeta A B C := by
  change sourceBeta e (0, (0, A)) (0, (0, B)) (0, (0, C)) = symmetricBlock A B C
  simp only [sourceBeta_components, map_zero, add_zero]

theorem sourceBeta_SRR (A : SymmetricPart) (r s : ShortSpace e) :
    sourceBeta e (symmetricInclusion e A) (shortInclusion e r) (shortInclusion e s) =
      sourceSRR e A r s := by
  change sourceBeta e (0, (0, A)) (0, (r, 0)) (0, (s, 0)) = sourceSRR e A r s
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, zero_add, add_zero]

theorem sourceBeta_RRR (r s t : ShortSpace e) :
    sourceBeta e (shortInclusion e r) (shortInclusion e s) (shortInclusion e t) =
      shortCubic e r s t := by
  change sourceBeta e (0, (r, 0)) (0, (s, 0)) (0, (t, 0)) = shortCubic e r s t
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, zero_add, add_zero]

theorem sourceBeta_SWW (A : SymmetricPart) (v w : MinusSpace) :
    sourceBeta e (symmetricInclusion e A) (minusInclusion e v) (minusInclusion e w) =
      sourceSWW A v w := by
  change sourceBeta e (0, (0, A)) (v, (0, 0)) (w, (0, 0)) = sourceSWW A v w
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, zero_add, add_zero]

theorem sourceBeta_RWW (r : ShortSpace e) (v w : MinusSpace) :
    sourceBeta e (shortInclusion e r) (minusInclusion e v) (minusInclusion e w) =
      sourceRWW e r v w := by
  change sourceBeta e (0, (r, 0)) (v, (0, 0)) (w, (0, 0)) = sourceRWW e r v w
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, zero_add, add_zero]

theorem sourceBeta_SSR (A B : SymmetricPart) (r : ShortSpace e) :
    sourceBeta e (symmetricInclusion e A) (symmetricInclusion e B) (shortInclusion e r) = 0 := by
  change sourceBeta e (0, (0, A)) (0, (0, B)) (0, (r, 0)) = 0
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, add_zero]

theorem sourceBeta_SSW (A B : SymmetricPart) (v : MinusSpace) :
    sourceBeta e (symmetricInclusion e A) (symmetricInclusion e B) (minusInclusion e v) = 0 := by
  change sourceBeta e (0, (0, A)) (0, (0, B)) (v, (0, 0)) = 0
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, add_zero]

theorem sourceBeta_RRW (r s : ShortSpace e) (v : MinusSpace) :
    sourceBeta e (shortInclusion e r) (shortInclusion e s) (minusInclusion e v) = 0 := by
  change sourceBeta e (0, (r, 0)) (0, (s, 0)) (v, (0, 0)) = 0
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, add_zero]

theorem sourceBeta_SRW (A : SymmetricPart) (r : ShortSpace e) (v : MinusSpace) :
    sourceBeta e (symmetricInclusion e A) (shortInclusion e r) (minusInclusion e v) = 0 := by
  change sourceBeta e (0, (0, A)) (0, (r, 0)) (v, (0, 0)) = 0
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, add_zero]

theorem sourceBeta_WWW (u v w : MinusSpace) :
    sourceBeta e (minusInclusion e u) (minusInclusion e v) (minusInclusion e w) = 0 := by
  change sourceBeta e (u, (0, 0)) (v, (0, 0)) (w, (0, 0)) = 0
  simp only [sourceBeta_components, map_zero, LinearMap.zero_apply, add_zero]

/-- Positivity on the actual 196884-dimensional sum supplies duality. -/
theorem sourceGamma_nondegenerate : (gamma e).Nondegenerate :=
  nondegenerate_of_positive _ (gamma_pos e)

/-- The unique multiplication recovered from the exact source forms. -/
def sourceProduct : OrthogonalSpace e →ₗ[ℝ] OrthogonalSpace e →ₗ[ℝ] OrthogonalSpace e :=
  dualProduct (gamma e) (sourceGamma_nondegenerate e) (sourceBeta e)

theorem gamma_sourceProduct (x y z : OrthogonalSpace e) :
    gamma e (sourceProduct e x y) z = sourceBeta e x y z :=
  gamma_dualProduct _ _ _ x y z

theorem sourceProduct_comm (x y : OrthogonalSpace e) :
    sourceProduct e x y = sourceProduct e y x :=
  dualProduct_comm _ _ _ (sourceBeta_swap_left e) x y

theorem sourceProduct_invariant_form (x y z : OrthogonalSpace e) :
    gamma e (sourceProduct e x y) z = gamma e x (sourceProduct e y z) :=
  dualProduct_invariant_form _ _ (gamma_symmetric e) _
    (fun a b c => (sourceBeta_swap_left e a b c).trans (sourceBeta_swap_right e b a c)) x y z

/-- The two-form stabilizer, pending instantiation of the fixed source comparison. -/
def sourceFormStabilizer : Subgroup (OrthogonalSpace e ≃ₗ[ℝ] OrthogonalSpace e) :=
  formStabilizer (gamma e) (sourceBeta e)

theorem sourceFormStabilizer_eq_productStabilizer :
    sourceFormStabilizer e = productStabilizer (gamma e) (sourceProduct e) :=
  formStabilizer_eq_productStabilizer _ _ _

end Sporadic.Monster.Construction.Griess
