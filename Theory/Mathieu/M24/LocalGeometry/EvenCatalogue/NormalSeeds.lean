module

public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds.NativeNormalizers
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds.QuotientBounds
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.OctadSeeds
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.OvergroupData

/-!
# Normal solvable seeds in the three native M₂₄ local families

Explicit native conjugations identify the two elementary normalizers with the
standard trio and sextet stabilizers. Their actual affine and column actions
exclude nine from the order of every normal solvable subgroup. Combining these
bounds with the octad calculation supplies the complete `NormalSeedBounds`
input, independently of exhaustive ambient normalizer coverage.

Source: Aschbacher–Smith 15.3.41–42, printed p.1138; GLS3, Table 5.3e.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue

/-- Neither of the actual two elementary normalizers admits a normal solvable
subgroup of order divisible by nine. -/
theorem elementary_normalizer_seed_bounds (k : Fin 2)
    (D : Subgroup (EvenCandidates.localGroup k))
    (hn : D.Normal) (hs : Group.IsSolvable D) : ¬ 9 ∣ Nat.card D := by
  fin_cases k
  · exact NormalSeeds.transport_bound NormalSeeds.trioNormalizerEquiv
      NormalSeeds.trio_normal_solvable_not_nine D hn hs
  · exact NormalSeeds.transport_bound NormalSeeds.sextetNormalizerEquiv
      NormalSeeds.sextet_normal_solvable_not_nine D hn hs

/-- The unconditional normal-seed bounds for the octad, trio and sextet families. -/
theorem normalSeedBounds : NormalSeedBounds :=
  ⟨octad_normal_solvable_not_nine, elementary_normalizer_seed_bounds⟩

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
