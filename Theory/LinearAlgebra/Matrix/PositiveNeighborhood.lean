module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

/-!
# Stability of positive quadratic forms

Near a real positive definite matrix, all quadratic evaluations on nonzero
vectors remain positive. Nearby matrices need not be symmetric; only their
quadratic forms are constrained. Joint continuity on matrices times the
compact unit sphere gives one neighborhood working for all unit vectors.
Normalize any nonzero vector and use quadratic homogeneity to extend the bound.

This supplies the finite-dimensional local comparison of metric slices used
for Colding–Minicozzi width continuity, following equation (1.28).
-/

open Set Filter
open scoped Topology
namespace Matrix
variable {ι : Type*} [Fintype ι]

public theorem PosDef.eventually_pos_quadratic {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∀ᶠ B in 𝓝 A, ∀ v : ι → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (B *ᵥ v) := by
  have hunit : ∀ᶠ B in 𝓝 A, ∀ v ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < v ⬝ᵥ (B *ᵥ v) := by
    apply (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      intro hz
      simp [hz] at hv
    have hp : 0 < v ⬝ᵥ (A *ᵥ v) := by simpa using hA.dotProduct_mulVec_pos hv0
    have hc : Continuous (fun p : Matrix ι ι ℝ × (ι → ℝ) => p.2 ⬝ᵥ (p.1 *ᵥ p.2)) := by
      unfold dotProduct mulVec
      fun_prop
    exact (hc.continuousAt (x := (A, v))).eventually (Ioi_mem_nhds hp)
  filter_upwards [hunit] with B hB v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [mem_sphere_iff_norm, norm_smul, hn.ne']
  have hp := hB _ hu
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hp
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp
    ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp)
end Matrix
