module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalStructure
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Reduction
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.GroupTheory.SolvableResidual

/-!
# Ree local solvable residuals from radical commutators

For `m ≥ 1`, the concrete Suzuki quotient is perfect by its proved simplicity
and nonsolvability. A surjection from the Suzuki-side fixed seed with the
specified root radical as kernel makes the seed perfect as soon as that
radical lies in the seed's derived subgroup. Its solvable residual is then
the whole seed. The matrix-preserving `seedEquiv` transfers this conclusion
to the published subgroup of `Model m`.

The corresponding linear-side residual uses the existing perfectness theorem
in `LargeLocalSeeds.LinearCore.Reduction`; its root work is not duplicated.
All seed perfectness and residual statements here are conditional reductions.
The Suzuki radical commutator inclusion is still a separate root calculation;
the projection, its surjectivity and its exact kernel are also explicit.
Neither a two-group kernel nor a perfect quotient alone implies perfectness.

Source: Aschbacher–Smith, F.1.12(II)(i) and its proof, printed pp.263–264
of `refs/quasithin.pdf`. The solvable residual is the intersection of the
derived series, distinct from O^{2′}, O² and O₂. No perfectness statement is
made at the binary endpoint, which belongs to F.1.12(II)(ii).
-/

public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal
open Subgroup LargeLocalSeeds BenderSuzuki.MatrixGroups

/-- Perfectness of the exact Suzuki matrix quotient for every large Ree field. -/
theorem suzukiQuotient_perfect (m : ℕ) (hm : 1 ≤ m) :
    Group.IsPerfect (SuzukiMatrixGroup m) := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  constructor
  rcases (inferInstance : (commutator (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top
      with h | h
  · exfalso
    apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    exact ⟨⟨1, (derivedSeries_one _).trans h⟩⟩
  · exact h

/-- The perfect Suzuki quotient lifts when its kernel lies in the derived subgroup. -/
theorem suzukiSeed_perfect_of_projection_and_radical_le_commutator
    {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hR : seedRadical d .suzuki ≤ commutator (standardSeed d .suzuki)) :
    Group.IsPerfect (standardSeed d .suzuki) := by
  let := suzukiQuotient_perfect m hm
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective π hπ
  rw [hker, sup_eq_right.mpr hR] at h
  exact ⟨h⟩

/-- Radical generation by local commutators suffices for the lifting criterion. -/
theorem suzukiSeed_perfect_of_projection_and_full_commutator
    {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hR : seedRadical d .suzuki ≤
      ⁅seedRadical d .suzuki, (⊤ : Subgroup (standardSeed d .suzuki))⁆) :
    Group.IsPerfect (standardSeed d .suzuki) :=
  suzukiSeed_perfect_of_projection_and_radical_le_commutator hm d π hπ hker
    (hR.trans (Subgroup.commutator_mono le_top le_rfl))

/-- The intrinsic solvable residual of the fixed seed is the whole seed. -/
theorem suzukiSeed_solvableResidual_of_projection_and_radical_le_commutator
    {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hR : seedRadical d .suzuki ≤ commutator (standardSeed d .suzuki)) :
    solvableResidual (standardSeed d .suzuki) = ⊤ := by
  let := suzukiSeed_perfect_of_projection_and_radical_le_commutator hm d π hπ hker hR
  exact solvableResidual_eq_top

/-- Transport to the published Suzuki-side subgroup of the concrete Model. -/
theorem suzuki_perfect_of_projection_and_radical_le_commutator
    {m : ℕ} (hm : 1 ≤ m)
    (π : standardSeed (canonicalLocalBlockInput m) .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π)
    (hker : π.ker = seedRadical (canonicalLocalBlockInput m) .suzuki)
    (hR : seedRadical (canonicalLocalBlockInput m) .suzuki ≤
      commutator (standardSeed (canonicalLocalBlockInput m) .suzuki)) :
    Group.IsPerfect (seed m .suzuki) := by
  let := suzukiSeed_perfect_of_projection_and_radical_le_commutator hm
    (canonicalLocalBlockInput m) π hπ hker hR
  exact Group.IsPerfect.ofSurjective (f := (seedEquiv m .suzuki).toMonoidHom)
    (seedEquiv m .suzuki).surjective

/-- The ambient image of the solvable residual equals the concrete Suzuki seed. -/
theorem suzuki_solvableResidual_eq_seed_of_projection_and_radical_le_commutator
    {m : ℕ} (hm : 1 ≤ m)
    (π : standardSeed (canonicalLocalBlockInput m) .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π)
    (hker : π.ker = seedRadical (canonicalLocalBlockInput m) .suzuki)
    (hR : seedRadical (canonicalLocalBlockInput m) .suzuki ≤
      commutator (standardSeed (canonicalLocalBlockInput m) .suzuki)) :
    (solvableResidual (seed m .suzuki)).map (seed m .suzuki).subtype = seed m .suzuki := by
  let := suzuki_perfect_of_projection_and_radical_le_commutator hm π hπ hker hR
  rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]

/-- Reuse the existing linear perfectness reduction for the second residual. -/
theorem linear_solvableResidual_eq_seed_of_projection_and_full_commutator
    {m : ℕ} (hm : 1 ≤ m)
    (π : standardSeed (canonicalLocalBlockInput m) .linear →* LinearQuotient m)
    (hπ : Function.Surjective π)
    (hker : π.ker = seedRadical (canonicalLocalBlockInput m) .linear)
    (hR : seedRadical (canonicalLocalBlockInput m) .linear ≤
      ⁅seedRadical (canonicalLocalBlockInput m) .linear,
        (⊤ : Subgroup (standardSeed (canonicalLocalBlockInput m) .linear))⁆) :
    (solvableResidual (seed m .linear)).map (seed m .linear).subtype = seed m .linear := by
  let := linearSeed_perfect_of_projection_and_full_commutator hm
    (canonicalLocalBlockInput m) π hπ hker hR
  let := Group.IsPerfect.ofSurjective (f := (seedEquiv m .linear).toMonoidHom)
    (seedEquiv m .linear).surjective
  rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]

end ReeF4.Parabolics.OuterLocal
