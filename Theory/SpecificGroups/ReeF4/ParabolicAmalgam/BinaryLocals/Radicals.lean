module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalStructure

/-!
# Root radicals under the fixed-seed comparison

View the specified root radical inside its containing seed. It is a two-group,
and the matrix-preserving comparison with `LargeLocalSeeds.standardSeed`
carries the corresponding radical exactly onto it. This permits a projection
constructed in either presentation to retain its exact kernel.

No relative normality or identification with O₂ is assumed here. Those follow
from the local projections. Source: the local quotients in Aschbacher–Smith
F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics
open LargeLocalSeeds Subgroup

/-- The root-defined radical as a subgroup of its containing fixed seed. -/
def radicalInSeed (m : ℕ) (s : Side) : Subgroup (seed m s) :=
  (radical m s).subgroupOf (seed m s)

theorem radicalInSeed_isPGroup (m : ℕ) (s : Side) :
    IsPGroup 2 (radicalInSeed m s) :=
  (radical_isPGroup m s).comap_subtype

theorem radicalInSeed_map (m : ℕ) (s : Side) :
    (radicalInSeed m s).map (seed m s).subtype = radical m s :=
  map_subgroupOf_eq_of_le ((radical_le_unipotent m s).trans (unipotent_le_seed m s))

/-- The fixed-seed comparison preserves the specified root radical. -/
@[simp] theorem radicalInSeed_comap_seedEquiv (m : ℕ) (s : Side) :
    (radicalInSeed m s).comap (seedEquiv m s).toMonoidHom =
      seedRadical (canonicalLocalBlockInput m) s := by
  ext x
  change toSplitGroup m (seedEquiv m s x) ∈ splitRadical m s ↔
    x.val.val ∈ splitRadical m s
  rw [seedEquiv_coe]

theorem seedRadical_map_seedEquiv (m : ℕ) (s : Side) :
    (seedRadical (canonicalLocalBlockInput m) s).map (seedEquiv m s).toMonoidHom =
      radicalInSeed m s := by
  rw [← radicalInSeed_comap_seedEquiv]
  exact map_comap_eq_self_of_surjective (seedEquiv m s).surjective _

end ReeF4.Parabolics
