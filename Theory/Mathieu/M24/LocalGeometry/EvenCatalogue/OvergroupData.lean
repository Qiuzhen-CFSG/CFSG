module

public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue
public import Theory.Mathieu.M24.LocalGeometry.EvenCandidates
public import Theory.Mathieu.M24.LocalGeometry.Defs
public import Mathlib.GroupTheory.Solvable

/-!
# Geometric overgroups and normal solvable subgroups of M₂₄ locals

The normalizer calculation needed by maximal characteristic-two arguments
is containment in an octad stabilizer or one of the two explicit elementary
normalizers. It does not require identifying each smaller normalizer.
The independent normal-subgroup calculation excludes a factor of nine from
solvable normal subgroups of these three geometric families.

These are explicit proof obligations, not assertions about the model.
Source: GLS3, Table 5.3e; Aschbacher--Smith, 15.3.41--42, printed p.1138.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue

/-- Each listed full ambient normalizer lies in one of the geometric locals. -/
def NormalizerOvergroups : Prop :=
  ∀ i : Fin 22,
    (∃ O : Octad, localGroup i ≤ octadStabilizer O) ∨
      ∃ k : Fin 2, localGroup i ≤ EvenCandidates.localGroup k

/-- The intrinsic normal solvable subgroups of the three local families
have three-part at most three. Only the exclusion of nine is requested. -/
def NormalSeedBounds : Prop :=
  (∀ (O : Octad) (D : Subgroup (octadStabilizer O)),
    D.Normal → Group.IsSolvable D → ¬ 9 ∣ Nat.card D) ∧
  (∀ (k : Fin 2) (D : Subgroup (EvenCandidates.localGroup k)),
    D.Normal → Group.IsSolvable D → ¬ 9 ∣ Nat.card D)

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
