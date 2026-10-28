module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.Parabolics
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.FixedProducts
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.DiagonalTorus

/-!
# The root-defined Borel and the intrinsic unipotent normalizer

The root Borel is the intersection of the positive split root Borel with the
supplied exceptional fixed group. The existing model equivalence is the identity
on the underlying split matrices, so it identifies this subgroup and the actual
positive unipotent subgroup with their canonical counterparts. Normalizer
functoriality therefore transports any proved normalizer identity exactly.

For the reverse inclusion, it suffices that the coroot-word torus lies in the
proved diagonal torus. The remaining inclusion is the separate fixed-group
normalizer bound. Both premises stay explicit: no intrinsic normalizer is
identified with the root Borel merely by definition.

Source: GLS3, Theorems 2.3.4(c) and 2.6.5(d),
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity
open Subgroup LargeLocalSeeds
variable {m : ℕ}

/-- The fixed intersection of the root-defined positive split Borel. -/
noncomputable def rootBorel (d : LocalBlockInput m) : Subgroup d.fixedGroup :=
  (Parabolics.splitBorel m).subgroupOf d.fixedGroup

private theorem modelEquiv_map_split_intersection (d : LocalBlockInput m)
    (H : Subgroup (SplitGroup m)) :
    (H.subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom =
      H.comap (toSplitGroup m) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change toSplitGroup m (d.modelEquiv y) ∈ H
    rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    refine ⟨d.modelEquiv.symm x, ?_, d.modelEquiv.apply_symm_apply x⟩
    change (d.modelEquiv.symm x).val ∈ H
    rw [Parabolics.modelEquiv_symm_coe]
    simpa only [Subgroup.mem_comap, toSplitGroup_apply] using hx

/-- The existing matrix-preserving model equivalence identifies the two root Borels. -/
theorem rootBorel_map_modelEquiv (d : LocalBlockInput m) :
    (rootBorel d).map d.modelEquiv.toMonoidHom = Parabolics.borel m :=
  modelEquiv_map_split_intersection d (Parabolics.splitBorel m)

/-- The same equivalence identifies the intrinsic positive unipotent normalizers. -/
theorem signedBorelNormalizer_positive_map_modelEquiv (d : LocalBlockInput m) :
    (signedBorelNormalizer d true).map d.modelEquiv.toMonoidHom =
      normalizer (Parabolics.unipotent m) := by
  change (normalizer (standardUnipotent d)).map d.modelEquiv.toMonoidHom = _
  rw [map_normalizer_eq_of_bijective _ d.modelEquiv.bijective,
    standardUnipotent, modelEquiv_map_split_intersection]
  rfl

/-- Transport an actual normalizer identity through the matrix-preserving equivalence. -/
theorem signedBorelNormalizer_eq_rootBorel_of_model (d : LocalBlockInput m)
    (h : normalizer (Parabolics.unipotent m) = Parabolics.borel m) :
    signedBorelNormalizer d true = rootBorel d := by
  apply (Subgroup.map_injective (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective)
  rw [signedBorelNormalizer_positive_map_modelEquiv, rootBorel_map_modelEquiv, h]

/-- The coroot realization and the fixed normalizer bound together identify the intrinsic Borel. -/
theorem signedBorelNormalizer_eq_rootBorel_of_splitTorus_and_bound (d : LocalBlockInput m)
    (hT : Parabolics.splitTorus m ≤ Parabolics.diagonalTorus m)
    (hN : normalizer (Parabolics.unipotent m) ≤ Parabolics.borel m) :
    signedBorelNormalizer d true = rootBorel d := by
  apply signedBorelNormalizer_eq_rootBorel_of_model d
  apply le_antisymm hN
  exact Parabolics.borel_le_unipotent_normalizer_of_splitTorus m
    (Parabolics.splitTorus_le_unipotent_normalizer_of_le_diagonalTorus m hT)

end ReeF4.LocalBlockInput.PairRigidity
end
