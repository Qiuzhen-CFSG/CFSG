module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.Residual
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Projection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.CommutatorGeneration
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry

/-!
# Perfect local factors in the large Ree groups

For `m ≥ 1`, the Suzuki-side root radical lies in the derived subgroup of
the canonical fixed seed. The concrete Levi projection has exactly this
radical as kernel and has perfect Suzuki image, so the seed is perfect.
The linear side uses its existing projection and commutator-generation
theorems through `LinearCore.Reduction`.

The matrix-preserving `seedEquiv` transports these conclusions to the two
published subgroups of `Model m`. Their proved identification with the
embedded prime-to-two residuals of the parabolics then gives perfectness
and solvable-residual equality for the actual local factors. All projection,
radical-commutator and seed-identification premises are discharged.

This supplies `Lᵢ = Lᵢ∞` for the Ree case of Aschbacher–Smith F.1.12(II)(i),
printed pp.263–264 of `refs/quasithin.pdf`. The containment of the specified
positive subgroup in each local factor is `unipotent_le_localFactor`.
The solvable residual is distinct from O^{2′}, O² and O₂; the identification
of a seed with O^{2′} uses the independent root-geometry theorem. These
perfectness conclusions exclude the binary endpoint `m = 0`.
-/

public section

namespace ReeF4.Parabolics.OuterLocal

open Subgroup LargeLocalSeeds BenderSuzuki.MatrixGroups

/-- The actual Suzuki radical commutator calculation discharges the remaining
perfectness premise for any projection with the specified root kernel. -/
theorem suzukiSeed_perfect_of_projection
    {m : ℕ} (hm : 1 ≤ m)
    (π : standardSeed (canonicalLocalBlockInput m) .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π)
    (hker : π.ker = seedRadical (canonicalLocalBlockInput m) .suzuki) :
    Group.IsPerfect (standardSeed (canonicalLocalBlockInput m) .suzuki) :=
  suzukiSeed_perfect_of_projection_and_radical_le_commutator hm
    (canonicalLocalBlockInput m) π hπ hker (SuzukiCommutators.radical_le_commutator hm)

/-- The canonical Suzuki-side fixed seed is perfect, using its concrete Levi
projection and the proved radical commutators. -/
theorem suzukiSeed_perfect {m : ℕ} (hm : 1 ≤ m) :
    Group.IsPerfect (standardSeed (canonicalLocalBlockInput m) .suzuki) :=
  suzukiSeed_perfect_of_projection hm
    (SuzukiLeviProjection.projection (canonicalLocalBlockInput m))
    (SuzukiLeviProjection.projection_surjective (canonicalLocalBlockInput m))
    (SuzukiLeviProjection.projection_ker (canonicalLocalBlockInput m))

/-- The intrinsic solvable residual is the whole canonical Suzuki-side seed. -/
theorem suzukiSeed_solvableResidual_eq_top {m : ℕ} (hm : 1 ≤ m) :
    solvableResidual (standardSeed (canonicalLocalBlockInput m) .suzuki) = ⊤ := by
  let := suzukiSeed_perfect hm
  exact solvableResidual_eq_top

/-- Both published fixed seeds in the concrete Ree carrier are perfect. -/
theorem seed_perfect {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    Group.IsPerfect (seed m s) := by
  have h : Group.IsPerfect (standardSeed (canonicalLocalBlockInput m) s) := by
    cases s with
    | suzuki => exact suzukiSeed_perfect hm
    | linear =>
      exact linearSeed_perfect_of_projection_and_full_commutator hm
        (canonicalLocalBlockInput m)
        (LinearProjection.projection hm (canonicalLocalBlockInput m))
        (LinearProjection.projection_surjective hm (canonicalLocalBlockInput m))
        (LinearProjection.projection_ker hm (canonicalLocalBlockInput m))
        (seedRadical_linear_le_commutator hm (canonicalLocalBlockInput m))
  exact Group.IsPerfect.ofSurjective (f := (seedEquiv m s).toMonoidHom)
    (seedEquiv m s).surjective

/-- The intrinsic solvable residual of either published fixed seed is full. -/
theorem seed_solvableResidual_eq_top {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    solvableResidual (seed m s) = ⊤ := by
  let := seed_perfect hm s
  exact solvableResidual_eq_top

/-- The solvable residual embedded in the Ree carrier is the original seed. -/
theorem seed_solvableResidual_eq_seed {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    (solvableResidual (seed m s)).map (seed m s).subtype = seed m s := by
  rw [seed_solvableResidual_eq_top hm s, ← MonoidHom.range_eq_map, range_subtype]

/-- The source local factor O^{2′}(Pᵢ), embedded in `Model m`, is perfect. -/
theorem localFactor_perfect {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    Group.IsPerfect (localFactor m s) := by
  rw [← seed_eq_localFactor]
  exact seed_perfect hm s

/-- The actual source local factor has full intrinsic solvable residual. -/
theorem localFactor_solvableResidual_eq_top {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    solvableResidual (localFactor m s) = ⊤ := by
  let := localFactor_perfect hm s
  exact solvableResidual_eq_top

/-- The Ree local-factor equality `Lᵢ∞ = Lᵢ` in the ambient carrier, with
both factors and the literal inclusion maps retained. -/
theorem localFactor_solvableResidual_eq_self {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    (solvableResidual (localFactor m s)).map (localFactor m s).subtype =
      localFactor m s := by
  rw [localFactor_solvableResidual_eq_top hm s, ← MonoidHom.range_eq_map, range_subtype]

end ReeF4.Parabolics.OuterLocal
