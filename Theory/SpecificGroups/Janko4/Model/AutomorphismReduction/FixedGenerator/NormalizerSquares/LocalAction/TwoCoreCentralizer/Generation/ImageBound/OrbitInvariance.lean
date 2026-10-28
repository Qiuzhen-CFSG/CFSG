module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.Orbit
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance.Quadratic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance.MixedRank
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance.RankCensus

/-!
# Intrinsic restrictions on the full centralizer's homology action

The entire literal centralizer preserves the nonzero singular locus of the
ambient quadratic form. The distinguished local orbit lies in that locus,
so its images under the full centralizer also lie there.

The contraction rank is also preserved by the full centralizer, and MixedRank
identifies it with an explicit forty-by-fifty matrix rank. RankCensus proves
that the distinguished orbit is exactly the rank-sixteen fibre. Combining
these results proves `homologyAction_preserves_distinguishedOrbit` for every
element of the entire centralizer. The quadratic statements alone do not
exclude movement into another singular local orbit.
In particular, no equality of the local subgroup with the full centralizer,
normalization of its image, or two-core identification is assumed.

Source motivation: GLS3, Table 5.3i, printed p.270. It does not identify this
natural-module homology with the Frattini quotient of the local two-core.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation

/-- Nonzero singular classes for the ambient quadratic form. -/
def nonzeroSingularHomology : Set NaturalHomology :=
  {v | v ≠ 0 ∧ OrbitQuadratic.homologyValue v = 0}

theorem distinguishedOrbit_subset_nonzeroSingularHomology :
    distinguishedOrbit ⊆ nonzeroSingularHomology := by
  intro v hv
  exact ⟨fun h => zero_not_mem_distinguishedOrbit (h ▸ hv),
    OrbitQuadratic.distinguishedOrbit_value_zero v hv⟩

/-- A genuine restriction from membership in the entire literal matrix group. -/
theorem homologyAction_preserves_nonzeroSingularHomology
    (c : involutionCentralizer) (v : NaturalHomology) (hv : v ∈ nonzeroSingularHomology) :
    (homologyAction c : Module.End (ZMod 2) NaturalHomology) v ∈ nonzeroSingularHomology := by
  refine ⟨?_, (OrbitQuadratic.homologyValue_invariant c v).trans hv.2⟩
  intro h
  apply hv.1
  have he := congrArg
    (fun w => (↑(homologyAction c)⁻¹ : Module.End (ZMod 2) NaturalHomology) w) h
  simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply, map_zero] using he

/-- The distinguished orbit cannot be moved into the nonsingular locus by C. -/
theorem homologyAction_distinguishedOrbit_mem_nonzeroSingularHomology
    (c : involutionCentralizer) (v : NaturalHomology) (hv : v ∈ distinguishedOrbit) :
    (homologyAction c : Module.End (ZMod 2) NaturalHomology) v ∈ nonzeroSingularHomology :=
  homologyAction_preserves_nonzeroSingularHomology c v
    (distinguishedOrbit_subset_nonzeroSingularHomology hv)

/-- Assembly from the finite rank-fibre identification. The rank invariant is
already proved for every element of the entire literal centralizer; the finite
identification is supplied by RankCensus in the unconditional theorem below. -/
theorem homologyAction_preserves_distinguishedOrbit_of_contraction_rank
    (hcharacter : ∀ h : NaturalHomology,
      h ∈ distinguishedOrbit ↔ ContractionRank.rank h = 16)
    (c : involutionCentralizer) (v : NaturalHomology) (hv : v ∈ distinguishedOrbit) :
    (homologyAction c : Module.End (ZMod 2) NaturalHomology) v ∈ distinguishedOrbit := by
  apply (hcharacter _).mpr
  exact (ContractionRank.rank_invariant c v).trans ((hcharacter v).mp hv)

/-- The entire literal involution centralizer preserves the distinguished local
orbit, characterized intrinsically as the contraction-rank-sixteen fibre. -/
theorem homologyAction_preserves_distinguishedOrbit
    (c : involutionCentralizer) (v : NaturalHomology) (hv : v ∈ distinguishedOrbit) :
    (homologyAction c : Module.End (ZMod 2) NaturalHomology) v ∈ distinguishedOrbit :=
  homologyAction_preserves_distinguishedOrbit_of_contraction_rank
    ContractionRank.Census.distinguishedOrbit_iff_rank_sixteen c v hv

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
