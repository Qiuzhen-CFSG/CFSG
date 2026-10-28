module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitCoverage

/-!
# Uniform split and fixed Ree Bruhat factors

The general-field split normal form uses all nonzero rank-one words, retaining
the torus in its middle factor. At `m = 0` the proved simple-Weyl normal form
maps into the same subgroup. These two results give coverage for every `m`.

Uniqueness of the actual middle matrix and of the two restricted unipotent
factors makes all three factors fixed when their product is fixed. The
matrix-preserving comparison with `Model m` gives the fixed normal form used
by the Borel-normalizer argument. No generation of fixed points is inferred
from split generation, and no simplicity or group-order premise is used.

Source: GLS3 1.11.5 and 2.3.5, `refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`; the full binary endpoint is the group in
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section

namespace ReeF4.Parabolics.Overlap
open Subgroup LargeLocalSeeds
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
noncomputable section
private local instance uniformBruhatIndexNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg

private theorem binaryWeyl_le_normalizerWords :
    Binary.FixedGeometry.BruhatCoverage.splitWeylSubgroup ≤ splitNormalizerWords 0 := by
  apply (closure_le _).mpr
  rintro x ⟨i, rfl⟩
  change Binary.FixedGeometry.simpleWord 0 [i] ∈ splitNormalizerWords 0
  have h := rankOneRepresentative_mem 0 (typeF4SimpleRootIndex i) 1
  simpa only [Binary.FixedGeometry.simpleWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, weylWord, rankOneRepresentative,
    Units.val_one, inv_one] using h

/-- Restricted split normal forms, uniformly including the binary field. -/
theorem exists_split_normal_form (m : ℕ) (g : SplitGroup m) :
    ∃ u ∈ splitUnipotent m, ∃ n ∈ splitNormalizerWords m,
      ∃ v ∈ rightUnipotent n, g = u * n * v := by
  rcases m with _ | m
  · obtain ⟨u, hu, n, hn, v, hv, he⟩ :=
      Binary.FixedGeometry.BruhatCoverage.exists_split_normal_form g
    exact ⟨u, hu, n, binaryWeyl_le_normalizerWords hn, v, hv, he⟩
  · exact LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.exists_split_normal_form
      (by omega) (fun _ hn => rootTransport_of_mem_splitNormalizerWords hn) g

/-- The actual fixed group has fixed positive outer factors and a fixed
middle factor in the full normalizer-word subgroup. -/
theorem exists_fixed_normal_form (m : ℕ) (g : Model m) :
    ∃ u ∈ unipotent m, ∃ n : Model m, toSplitGroup m n ∈ splitNormalizerWords m ∧
      ∃ v ∈ unipotent m, g = u * n * v := by
  let d := canonicalLocalBlockInput m
  obtain ⟨u, hu, n, hn, v, hv, he⟩ := exists_fixed_factors_of_split d
    (exists_split_normal_form m) middle_representative_unique (d.modelEquiv.symm g)
  refine ⟨d.modelEquiv u, ?_, d.modelEquiv n, ?_, d.modelEquiv v, ?_, ?_⟩
  · change toSplitGroup m (d.modelEquiv u) ∈ splitUnipotent m
    simpa only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe] using (show u.val ∈ splitUnipotent m from hu)
  · simpa only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe] using hn
  · change toSplitGroup m (d.modelEquiv v) ∈ splitUnipotent m
    simpa only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe] using (show v.val ∈ splitUnipotent m from hv)
  · simpa only [MulEquiv.apply_symm_apply, map_mul] using congrArg d.modelEquiv he

end
end ReeF4.Parabolics.Overlap
