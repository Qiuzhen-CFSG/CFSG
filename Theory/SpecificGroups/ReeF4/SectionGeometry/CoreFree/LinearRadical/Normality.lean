module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Normality

/-!
# Relative normality of the full Ree parabolic radicals

The root exchange calculation already proves that each split seed normalizes
its specified radical. Every coroot word belongs to the diagonal torus, whose
conjugation scales root parameters without changing their support. Thus the
full split parabolic, including the complementary torus, normalizes the radical.
Taking inverse images under the actual Ree inclusion gives relative normality
inside the fixed parabolic, with no simplicity hypothesis.

Source: GLS3, Theorem 2.6.5(d,g), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section

namespace ReeF4.SectionGeometry.LinearRadical

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open LargeLocalSeeds Parabolics Subgroup
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration

/-- Diagonal conjugation preserves the support of either specified radical. -/
theorem diagonalTorus_le_radical_normalizer (m : ℕ) (side : Side) :
    diagonalTorus m ≤ normalizer (splitRadical m side : Set (SplitGroup m)) := by
  rw [le_normalizer_iff]
  intro z hz x hx
  change z.val ∈ (diagonalTorusHom m).range at hz
  obtain ⟨u, hu⟩ := hz
  change (MulAut.conj z) x ∈ _
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨r, ((integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r :
      (CoefficientField m)ˣ) : CoefficientField m) * t, hr, ?_⟩
    apply Subtype.ext
    change z.val * F4Chevalley.rootCurve r t * z.val⁻¹ = _
    rw [← hu]
    simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe]
      using F4Chevalley.rootCurve_torus_conjugation u⁻¹ r t
  | one => simpa only [map_one] using (one_mem _)
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using inv_mem hx

/-- The complementary torus also normalizes the root radical. -/
theorem splitTorus_le_radical_normalizer (m : ℕ) (side : Side) :
    splitTorus m ≤ normalizer (splitRadical m side : Set (SplitGroup m)) := by
  rw [splitTorus_eq_diagonalTorus]
  exact diagonalTorus_le_radical_normalizer m side

/-- Normality in the full split parabolic, not just its smaller seed. -/
theorem splitParabolic_le_radical_normalizer (m : ℕ) (side : Side) :
    splitParabolic m side ≤ normalizer (splitRadical m side : Set (SplitGroup m)) :=
  sup_le (splitSeed_le_radical_normalizer m side)
    (splitTorus_le_radical_normalizer m side)

/-- Relative normality descends through the actual Ree inclusion. -/
theorem parabolic_le_radical_normalizer (m : ℕ) (side : Side) :
    parabolic m side ≤ normalizer (radical m side : Set (Model m)) :=
  (comap_mono (splitParabolic_le_radical_normalizer m side)).trans
    (le_normalizer_comap (toSplitGroup m))

theorem radical_le_parabolic (m : ℕ) (side : Side) :
    radical m side ≤ parabolic m side :=
  (radical_le_unipotent m side).trans
    ((unipotent_le_borel m).trans (borel_le_parabolic m side))

/-- The normal subgroup is the given root radical viewed inside its parabolic. -/
theorem radical_subgroupOf_normal (m : ℕ) (side : Side) :
    ((radical m side).subgroupOf (parabolic m side)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (radical_le_parabolic m side)).mpr
    (parabolic_le_radical_normalizer m side)

end ReeF4.SectionGeometry.LinearRadical
