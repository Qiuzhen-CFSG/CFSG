module

public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.Duality
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.Blocks
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.SignedBlocks
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.SourceForms
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Isometry

/-!
# The fixed Griess algebra and its automorphism carrier

The fixed space is the LocalC orthogonal sum instantiated with the proved
source Golay–Leech comparison. Its dimension is 196884. The trilinear form has
exactly the five blocks of Section 28, using actual short extraspecial lifts
and their descended spin operators. Signed descent and full symmetry are
proved in the imported block modules. No comparison, representation or form
remains a parameter of the carrier.

Positive nondegenerate duality recovers the unique commutative multiplication.
The group `Sporadic.Monster.GriessGroup` is the simultaneous stabilizer of the
positive and trilinear forms, equivalently the isometric algebra automorphisms.
The source coordinate and quotient equations are re-exported with the fixed
comparison. Local-group embeddings, finiteness and simplicity are separate
results, not inputs to this construction.

Source: Aschbacher, *Sporadic Groups*, Sections 27–28, especially 28.2,
28.4–28.6 and 28.7–28.12, printed pp. 150–154.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct Matrix
namespace Sporadic.Monster
open Construction Construction.LocalC Construction.Griess Construction.TrialitySpin

/-- The fixed real space from Section 27, using the actual source coordinate map. -/
abbrev GriessSpace := OrthogonalSpace sourceLatticeComparison

theorem griessSpace_finrank : Module.finrank ℝ GriessSpace = 196884 :=
  orthogonalSpace_finrank sourceLatticeComparison

/-- The orthogonal sum of the source symmetric, short and natural-spin forms. -/
def griessGamma : LinearMap.BilinForm ℝ GriessSpace := gamma sourceLatticeComparison

theorem griessGamma_components (x y : GriessSpace) :
    griessGamma x y = minusForm x.1 y.1 +
      shortForm sourceLatticeComparison x.2.1 y.2.1 + symmetricGamma x.2.2 y.2.2 := rfl

theorem griessGamma_symmetric (x y : GriessSpace) : griessGamma x y = griessGamma y x :=
  gamma_symmetric sourceLatticeComparison x y

theorem griessGamma_pos (x : GriessSpace) (hx : x ≠ 0) : 0 < griessGamma x x :=
  gamma_pos sourceLatticeComparison x hx

theorem griessGamma_nondegenerate : griessGamma.Nondegenerate :=
  sourceGamma_nondegenerate sourceLatticeComparison

/-- The exact symmetric trilinear form of 28.12 on the fixed source space. -/
def griessBeta : TrilinearForm GriessSpace := sourceBeta sourceLatticeComparison

theorem griessBeta_swap_left (x y z : GriessSpace) :
    griessBeta x y z = griessBeta y x z := sourceBeta_swap_left sourceLatticeComparison x y z

theorem griessBeta_swap_right (x y z : GriessSpace) :
    griessBeta x y z = griessBeta x z y := sourceBeta_swap_right sourceLatticeComparison x y z

theorem griessBeta_permute (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → GriessSpace) :
    griessBeta (v (σ 0)) (v (σ 1)) (v (σ 2)) = griessBeta (v 0) (v 1) (v 2) :=
  sourceBeta_permute sourceLatticeComparison σ v

/-- The five source blocks and their unscaled placements, now with every input fixed. -/
theorem griessBeta_components (x y z : GriessSpace) :
    griessBeta x y z =
      symmetricBeta x.2.2 y.2.2 z.2.2 +
      shortCubic sourceLatticeComparison x.2.1 y.2.1 z.2.1 +
      (sourceSRR sourceLatticeComparison x.2.2 y.2.1 z.2.1 +
        sourceSRR sourceLatticeComparison y.2.2 x.2.1 z.2.1 +
        sourceSRR sourceLatticeComparison z.2.2 x.2.1 y.2.1) +
      (sourceSWW x.2.2 y.1 z.1 + sourceSWW y.2.2 x.1 z.1 + sourceSWW z.2.2 x.1 y.1) +
      (sourceRWW sourceLatticeComparison x.2.1 y.1 z.1 +
        sourceRWW sourceLatticeComparison y.2.1 x.1 z.1 +
        sourceRWW sourceLatticeComparison z.2.1 x.1 y.1) := rfl

/-- Equation (28.1) paired with the third symmetric matrix. -/
theorem griessBeta_SSS (A B C : SymmetricPart) :
    griessBeta (symmetricInclusion sourceLatticeComparison A)
      (symmetricInclusion sourceLatticeComparison B) (symmetricInclusion sourceLatticeComparison C) =
      symmetricGamma (symmetricProduct A B) C :=
  sourceBeta_SSS sourceLatticeComparison A B C

/-- Equation (28.2) on the signed short vectors of the fixed source comparison. -/
theorem griessBeta_SRR (A : SymmetricPart) (r s : ShortLift sourceLatticeComparison) :
    griessBeta (symmetricInclusion sourceLatticeComparison A)
      (shortInclusion sourceLatticeComparison (shortVector sourceLatticeComparison r))
      (shortInclusion sourceLatticeComparison (shortVector sourceLatticeComparison s)) =
      symmetricGamma A (shortLiftTensor sourceLatticeComparison r) *
        shortForm sourceLatticeComparison
          (shortVector sourceLatticeComparison r) (shortVector sourceLatticeComparison s) :=
  (sourceBeta_SRR sourceLatticeComparison _ _ _).trans
    (sourceSRR_vector sourceLatticeComparison A r s)

/-- Equation (28.4), including its zero clause when the product is not short. -/
theorem griessBeta_RRR (r s t : ShortLift sourceLatticeComparison) :
    griessBeta
      (shortInclusion sourceLatticeComparison (shortVector sourceLatticeComparison r))
      (shortInclusion sourceLatticeComparison (shortVector sourceLatticeComparison s))
      (shortInclusion sourceLatticeComparison (shortVector sourceLatticeComparison t)) =
      shortForm sourceLatticeComparison
        (shortSourceProduct sourceLatticeComparison r s) (shortVector sourceLatticeComparison t) :=
  (sourceBeta_RRR sourceLatticeComparison _ _ _).trans
    (shortCubic_source sourceLatticeComparison r s t)

/-- Equation (28.5), with the trace coefficient exactly one eighth. -/
theorem griessBeta_SWW (A : SymmetricPart) (a b : NaturalSpace) (v w : SpinSpace) :
    griessBeta (symmetricInclusion sourceLatticeComparison A)
      (minusInclusion sourceLatticeComparison (a ⊗ₜ[ℝ] v))
      (minusInclusion sourceLatticeComparison (b ⊗ₜ[ℝ] w)) =
      ((a ᵥ* A.val) ⬝ᵥ b + Matrix.trace A.val * (a ⬝ᵥ b) / 8) * bothAxesDomain.form v w :=
  (sourceBeta_SWW sourceLatticeComparison _ _ _).trans (sourceSWW_tmul A a b v w)

/-- Equation (28.6) for every genuine short representative of the fixed lift.
The only premise identifies the chosen representative, not a form or action. -/
theorem griessBeta_RWW (r : ShortLift sourceLatticeComparison)
    (ξ : Atlas.Lattices.LeechShell 4)
    (hξ : shortReduction ξ = shortLiftClass sourceLatticeComparison r)
    (a b : NaturalSpace) (v w : SpinSpace) :
    griessBeta
      (shortInclusion sourceLatticeComparison (shortVector sourceLatticeComparison r))
      (minusInclusion sourceLatticeComparison (a ⊗ₜ[ℝ] v))
      (minusInclusion sourceLatticeComparison (b ⊗ₜ[ℝ] w)) =
      (a ⬝ᵥ b - 2 * (a ⬝ᵥ leechVector ξ.val) * (leechVector ξ.val ⬝ᵥ b)) *
        bothAxesDomain.form (SpinAction.imageRepresentation r.val v) w / 8 :=
  (sourceBeta_RWW sourceLatticeComparison _ _ _).trans
    (sourceRWW_representative sourceLatticeComparison r ξ hξ a b v w)

/-- The bilinear multiplication uniquely specified by the exact source forms. -/
def griessProduct : GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] GriessSpace :=
  sourceProduct sourceLatticeComparison

theorem gamma_griessProduct (x y z : GriessSpace) :
    griessGamma (griessProduct x y) z = griessBeta x y z :=
  gamma_sourceProduct sourceLatticeComparison x y z

theorem griessProduct_unique (m : GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] GriessSpace)
    (hm : ∀ x y z, griessGamma (m x y) z = griessBeta x y z) : m = griessProduct :=
  dualProduct_unique griessGamma griessGamma_nondegenerate griessBeta m hm

theorem griessProduct_comm (x y : GriessSpace) : griessProduct x y = griessProduct y x :=
  sourceProduct_comm sourceLatticeComparison x y

theorem griessProduct_invariant_form (x y z : GriessSpace) :
    griessGamma (griessProduct x y) z = griessGamma x (griessProduct y z) :=
  sourceProduct_invariant_form sourceLatticeComparison x y z

/-- The simultaneous stabilizer of the two fixed source forms. -/
def griessFormStabilizer : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
  formStabilizer griessGamma griessBeta

/-- The parameter-free Griess automorphism-group carrier, with its inherited group structure. -/
abbrev GriessGroup : Type := ↥griessFormStabilizer

theorem mem_griessFormStabilizer_iff (f : GriessSpace ≃ₗ[ℝ] GriessSpace) :
    f ∈ griessFormStabilizer ↔
      (∀ x y, griessGamma (f x) (f y) = griessGamma x y) ∧
      (∀ x y z, griessBeta (f x) (f y) (f z) = griessBeta x y z) := Iff.rfl

/-- The stabilizer equality of 28.12, for the fixed algebra and positive form. -/
theorem griessFormStabilizer_eq_productStabilizer :
    griessFormStabilizer = productStabilizer griessGamma griessProduct :=
  formStabilizer_eq_productStabilizer griessGamma griessGamma_nondegenerate griessBeta

/-- A linear equivalence belongs to the carrier exactly when it is an isometric
automorphism of the source multiplication. -/
theorem mem_griessFormStabilizer_iff_product (f : GriessSpace ≃ₗ[ℝ] GriessSpace) :
    f ∈ griessFormStabilizer ↔
      (∀ x y, griessGamma (f x) (f y) = griessGamma x y) ∧
      (∀ x y, griessProduct (f x) (f y) = f (griessProduct x y)) :=
  mem_formStabilizer_iff griessGamma griessGamma_nondegenerate griessBeta f

end Sporadic.Monster
