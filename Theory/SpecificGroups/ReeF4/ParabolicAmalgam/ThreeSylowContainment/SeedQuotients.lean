module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Reduction
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Nonsolvability of Ree seeds from their concrete Levi images

For a large Ree field the actual PSL₂ and Suzuki matrix targets are
nonsolvable. A surjection from either fixed seed therefore prevents that seed
from lying in a solvable overgroup. Only surjectivity is needed here: neither
the radical's order nor its identification with the intrinsic two-core enters
this argument. The construction of each surjection is a separate obligation.

Source: Aschbacher–Smith F.1.12(I)(5), printed p.263, and the proof of
Proposition 1.3.4, printed p.511, `refs/quasithin.pdf`.
-/

public section

namespace ReeF4.Parabolics.ThreeSylowContainment

open LargeLocalSeeds

/-- The root-defined linear seed is nonsolvable if its actual PSL₂ projection
is surjective. No kernel calculation is required for this consequence. -/
theorem linear_seed_not_isSolvable_of_surjective {m : ℕ} (hm : 1 ≤ m)
    (π : standardSeed (canonicalLocalBlockInput m) .linear →* LinearQuotient m)
    (hπ : Function.Surjective π) : ¬ Group.IsSolvable (seed m .linear) := by
  intro hs
  let _ : Group.IsSolvable (seed m .linear) := hs
  have hq : Group.IsSolvable (LinearQuotient m) :=
    Group.isSolvable_of_surjective
      (f := π.comp (seedEquiv m .linear).symm.toMonoidHom)
      (hπ.comp (seedEquiv m .linear).symm.surjective)
  let _ := linearQuotient_simple m hm
  let _ := linearQuotient_perfect m hm
  exact Group.IsPerfect.not_isSolvable (LinearQuotient m) hq

/-- The root-defined Suzuki seed is nonsolvable if its projection onto the
actual Suzuki matrix carrier is surjective. -/
theorem suzuki_seed_not_isSolvable_of_surjective {m : ℕ} (hm : 1 ≤ m)
    (π : standardSeed (canonicalLocalBlockInput m) .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) : ¬ Group.IsSolvable (seed m .suzuki) := by
  intro hs
  let _ : Group.IsSolvable (seed m .suzuki) := hs
  exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    (Group.isSolvable_of_surjective
      (f := π.comp (seedEquiv m .suzuki).symm.toMonoidHom)
      (hπ.comp (seedEquiv m .suzuki).symm.surjective))

end ReeF4.Parabolics.ThreeSylowContainment
