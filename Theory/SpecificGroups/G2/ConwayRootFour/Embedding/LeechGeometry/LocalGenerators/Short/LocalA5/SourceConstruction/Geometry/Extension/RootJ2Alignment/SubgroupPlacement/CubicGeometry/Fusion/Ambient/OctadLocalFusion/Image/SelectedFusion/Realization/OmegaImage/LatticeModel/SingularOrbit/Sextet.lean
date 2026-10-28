module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.ReducedKernel
public import Theory.AtlasPort.OtherSporadic.Conway.SextetIsometry
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayOctadTransitivity

/-!
# A compatible sextet in the marked octad centralizer

The distinguished sextet isometry commutes with the sign on a union of two
of its tetrads. Mathieu octad transitivity transports that octad to the
literal support of `golayBasis 0`. Conjugating the isometry by the resulting
integral coordinate permutation therefore gives a member of the required
centralizer.

The conjugating permutation is monomial. Since the original sextet isometry
is nonmonomial, its conjugate is nonmonomial as well. All maps here act on
the integral Leech lattice.

Source: Aschbacher, *Sporadic Groups* (1994), 25.3, p.133.
The sextet, Mathieu and monomial constructions are the existing ATLAS ports,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public noncomputable section

open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel

private theorem zeta_commutes_trio_sign (c : golay)
    (hc : support c.val = distinguishedTrio 0) :
    Commute zeta (signEmbedding (Multiplicative.ofAdd c)) := by
  have hc0 (p : Atlas.Codes.Omega) : c.val p = 0 ↔ p.1.1 ≠ 0 := by
    have h : c.val p ≠ 0 ↔ p.1.1 = 0 := by
      have hh := Finset.ext_iff.mp hc p
      simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and,
        distinguishedTrio_compatibility] using hh
    simpa only [not_not] using not_congr h
  have hs (x : leech) :
      rationalEmbedding ((signEmbedding (Multiplicative.ofAdd c)).val x).val =
        fun p => if p.1.1 = 0 then -rationalEmbedding x.val p else rationalEmbedding x.val p := by
    funext p
    change ((if c.val p = 0 then x.val p else -x.val p : ℤ) : ℚ) = _
    by_cases hp : p.1.1 = 0
    · rw [if_neg (fun hz => (hc0 p).mp hz hp), if_pos hp]
      simp [rationalEmbedding]
    · rw [if_pos ((hc0 p).mpr hp), if_neg hp]
      rfl
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (zeta.val ((signEmbedding (Multiplicative.ofAdd c)).val x)).val =
    rationalEmbedding ((signEmbedding (Multiplicative.ofAdd c)).val (zeta.val x)).val
  rw [zeta_agrees, hs, hs, zeta_agrees]
  funext p
  rcases p with ⟨a, k⟩
  simp only [sextetReflection_apply]
  by_cases h : a.1 = 0
  · simp only [h, if_true, Finset.sum_neg_distrib]
    ring
  · simp only [h, if_false]

/-- A sextet compatible with the marked octad supplies an actual
nonmonomial member of its integral Leech centralizer. -/
theorem exists_nonmonomial_centralizer :
    ∃ g : centralizer, g.val ∉ monomialSubgroup := by
  classical
  obtain ⟨c, hc8, hc⟩ := (octads_mem _).mp (distinguishedTrio_octads 0)
  have hB : support (golayBasis 0).val ∈ octads :=
    (octads_mem _).mpr ⟨golayBasis 0, ambientOctad_weight, rfl⟩
  obtain ⟨σ, hσ⟩ := mathieu24_octad_transitive (distinguishedTrio 0)
    (support (golayBasis 0).val) (distinguishedTrio_octads 0) hB
  let p := permutationEmbedding σ
  have hp : p ∈ monomialSubgroup := by
    refine ⟨SemidirectProduct.inr σ, ?_⟩
    exact DFunLike.congr_fun monomial_inr σ
  have he : golayPermutationEquiv σ c = golayBasis 0 := by
    apply Subtype.ext
    apply support_injective
    change support (coordinatePermutation σ.val c.val) = support (golayBasis 0).val
    rw [coordinatePermutation_support, hc, hσ]
  have ht : p * signEmbedding (Multiplicative.ofAdd c) * p⁻¹ = sign := by
    have h := DFunLike.congr_fun (sign_permutation_compatibility σ) (Multiplicative.ofAdd c)
    change signEmbedding (Multiplicative.ofAdd (golayPermutationEquiv σ c)) =
      p * signEmbedding (Multiplicative.ofAdd c) * p⁻¹ at h
    rw [he] at h
    exact h.symm
  let g : LeechIsometryGroup := p * zeta * p⁻¹
  have hg : g ∈ centralizer := by
    apply mem_centralizer.mpr
    have h := (zeta_commutes_trio_sign c hc).map (MulAut.conj p).toMonoidHom
    change Commute g (p * signEmbedding (Multiplicative.ofAdd c) * p⁻¹) at h
    rwa [ht] at h
  refine ⟨⟨g, hg⟩, ?_⟩
  intro h
  have hh := monomialSubgroup.mul_mem
    (monomialSubgroup.mul_mem (monomialSubgroup.inv_mem hp) h) hp
  have heq : p⁻¹ * g * p = zeta := by dsimp [g]; group
  rw [heq] at hh
  exact zeta_not_monomial hh

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

