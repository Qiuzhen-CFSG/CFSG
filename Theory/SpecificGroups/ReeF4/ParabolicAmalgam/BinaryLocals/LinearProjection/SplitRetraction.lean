module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Generation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction.Grading
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction.Normality
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges

/-!
# Retraction onto the actual end-node Levi

Relative normality of the specified root radical collects every element of
the split linear seed into a radical factor followed by a Levi factor. The
matrix grading proves that this Levi factor is unique. Choosing it defines
a homomorphism which fixes the Levi and has exactly the specified radical as
kernel. Both root supports are twist-stable, so uniqueness also proves that
the retraction commutes with the Ree twist.

At the binary endpoint, the proved positive-root exchanges and end-node Weyl
conjugation identities supply relative normality unconditionally. Thus
`splitRetraction` has no additional hypotheses. The construction for general
`m` retains relative normality as an explicit input.

Source: the standard root Levi construction underlying Aschbacher–Smith,
F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.BinaryLinear
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Subgroup

/-- Exceptional root duality preserves the specified linear radical support. -/
theorem isRadicalRoot_duality_linear {r : F4Chevalley.Root}
    (hr : IsRadicalRoot .linear r) :
    IsRadicalRoot .linear (exceptionalRootPermutation r) := by
  rcases isSeedRoot_radical_or_levi (isSeedRoot_duality .linear r (Or.inl hr.1)) with h | h
  · exact h
  · have hl := isLeviRoot_duality h
    rw [exceptionalRootPermutation_involutive] at hl
    exact (isRadicalRoot_not_isLeviRoot hr hl).elim

/-- Twist invariance of the existing root-generated radical. -/
theorem splitRadical_linear_invariant (m : ℕ) :
    (splitRadical m .linear).map (reeAutomorphism m).toMonoidHom =
      splitRadical m .linear := by
  have h : (splitRadical m .linear).map (reeAutomorphism m).toMonoidHom ≤
      splitRadical m .linear := by
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    change reeAutomorphism m (rootGeneratorInGroup m r t) ∈ splitRadical m .linear
    rw [reeAutomorphism_apply, reeTwist_rootGenerator]
    exact subset_closure ⟨_, _, isRadicalRoot_duality_linear hr, rfl⟩
  apply le_antisymm h
  intro x hx
  refine ⟨reeAutomorphism m x, h (mem_map_of_mem _ hx), ?_⟩
  simpa only [MulEquiv.coe_toMonoidHom, reeAutomorphism_apply] using
    reeTwist_involutive m x

private theorem radicalInSeed_twist_mem (m : ℕ) {x : splitSeed m .linear}
    (hx : x ∈ splitRadicalInSeed m) : seedTwist m x ∈ splitRadicalInSeed m := by
  change (seedTwist m x).val ∈ splitRadical m .linear
  rw [seedTwist_coe]
  have h := (splitRadical_linear_invariant m).le
    (mem_map_of_mem (reeAutomorphism m).toMonoidHom
      (show x.val ∈ splitRadical m .linear from hx))
  simpa only [MulEquiv.coe_toMonoidHom, reeAutomorphism_apply] using h

private theorem twist_leviInclusion (m : ℕ) (l : splitLevi m) :
    seedTwist m (leviInclusion m l) = leviInclusion m (leviTwist m l) := by
  apply Subtype.ext
  exact (seedTwist_coe m _).trans (leviTwist_coe m l).symm

private theorem radical_le_seed (m : ℕ) : splitRadical m .linear ≤ splitSeed m .linear :=
  (splitRadical_le_unipotent m .linear).trans (splitUnipotent_le_splitSeed m .linear)

/-- Relative normality collects every seed element into a radical factor followed
by a Levi factor. -/
theorem exists_levi_residue_of_normal (m : ℕ)
    (hN : (splitRadicalInSeed m).Normal) (x : splitSeed m .linear) :
    ∃ l : splitLevi m, x * (leviInclusion m l)⁻¹ ∈ splitRadicalInSeed m := by
  let := hN
  have hsup : splitRadicalInSeed m ⊔ (splitLevi m).subgroupOf (splitSeed m .linear) = ⊤ := by
    rw [splitRadicalInSeed, ← subgroupOf_sup (radical_le_seed m) (splitLevi_le_seed m),
      ← splitSeed_eq_radical_sup_levi, subgroupOf_self]
  have hx : x ∈ splitRadicalInSeed m ⊔ (splitLevi m).subgroupOf (splitSeed m .linear) := by
    rw [hsup]
    exact mem_top x
  obtain ⟨u, hu, l, hl, he⟩ := mem_sup_of_normal_left.mp hx
  refine ⟨⟨l.val, hl⟩, ?_⟩
  change x * l⁻¹ ∈ splitRadicalInSeed m
  rw [← he, mul_inv_cancel_right]
  exact hu

private theorem levi_residue_unique (m : ℕ) {x : splitSeed m .linear}
    {l k : splitLevi m}
    (hl : x * (leviInclusion m l)⁻¹ ∈ splitRadicalInSeed m)
    (hk : x * (leviInclusion m k)⁻¹ ∈ splitRadicalInSeed m) : l = k := by
  have hmem := (splitRadicalInSeed m).mul_mem ((splitRadicalInSeed m).inv_mem hl) hk
  have he : (x * (leviInclusion m l)⁻¹)⁻¹ * (x * (leviInclusion m k)⁻¹) =
      leviInclusion m l * (leviInclusion m k)⁻¹ := by group
  rw [he] at hmem
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  exact (Subgroup.disjoint_def.mp (splitRadical_disjoint_splitLevi m)) hmem
    ((splitLevi m).mul_mem l.property ((splitLevi m).inv_mem k.property))

private def leviFactor (m : ℕ) (hN : (splitRadicalInSeed m).Normal)
    (x : splitSeed m .linear) : splitLevi m :=
  Classical.choose (exists_levi_residue_of_normal m hN x)

private theorem leviFactor_residue (m : ℕ) (hN : (splitRadicalInSeed m).Normal)
    (x : splitSeed m .linear) :
    x * (leviInclusion m (leviFactor m hN x))⁻¹ ∈ splitRadicalInSeed m :=
  Classical.choose_spec (exists_levi_residue_of_normal m hN x)

/-- The genuine Levi-factor retraction, conditional only on relative normality
of the specified radical. The matrix intersection theorem supplies uniqueness. -/
def splitRetractionOfNormal (m : ℕ) (hN : (splitRadicalInSeed m).Normal) :
    splitSeed m .linear →* splitLevi m where
  toFun := leviFactor m hN
  map_one' := by
    apply levi_residue_unique m (leviFactor_residue m hN 1)
    simp only [map_one, inv_one, mul_one]
    exact (splitRadicalInSeed m).one_mem
  map_mul' x y := by
    apply levi_residue_unique m (leviFactor_residue m hN (x * y))
    have hx := leviFactor_residue m hN x
    have hy := hN.conj_mem _ (leviFactor_residue m hN y)
      (leviInclusion m (leviFactor m hN x))
    have hxy := (splitRadicalInSeed m).mul_mem hx hy
    convert hxy using 1
    simp only [map_mul]
    group

/-- The retraction removes exactly a left radical factor. -/
theorem splitRetractionOfNormal_residue (m : ℕ) (hN : (splitRadicalInSeed m).Normal)
    (x : splitSeed m .linear) :
    x * (leviInclusion m (splitRetractionOfNormal m hN x))⁻¹ ∈ splitRadicalInSeed m :=
  leviFactor_residue m hN x

/-- The chosen Levi factor of a Levi element is that element. -/
theorem splitRetractionOfNormal_levi (m : ℕ) (hN : (splitRadicalInSeed m).Normal)
    (l : splitLevi m) : splitRetractionOfNormal m hN (leviInclusion m l) = l := by
  apply levi_residue_unique m (splitRetractionOfNormal_residue m hN _)
  rw [mul_inv_cancel]
  exact (splitRadicalInSeed m).one_mem

/-- The kernel is the specified root radical, rather than a radical defined by
this projection. -/
theorem splitRetractionOfNormal_ker (m : ℕ) (hN : (splitRadicalInSeed m).Normal) :
    (splitRetractionOfNormal m hN).ker = splitRadicalInSeed m := by
  ext x
  change splitRetractionOfNormal m hN x = 1 ↔ x ∈ splitRadicalInSeed m
  constructor
  · intro hx
    have h := splitRetractionOfNormal_residue m hN x
    simpa only [hx, map_one, inv_one, mul_one] using h
  · intro hx
    apply levi_residue_unique m (splitRetractionOfNormal_residue m hN x)
    simpa only [map_one, inv_one, mul_one] using hx

/-- Invariance of the radical and Levi makes the retraction commute with the
actual Ree twist. -/
theorem splitRetractionOfNormal_twist (m : ℕ) (hN : (splitRadicalInSeed m).Normal)
    (x : splitSeed m .linear) :
    splitRetractionOfNormal m hN (seedTwist m x) =
      leviTwist m (splitRetractionOfNormal m hN x) := by
  apply levi_residue_unique m (splitRetractionOfNormal_residue m hN _)
  have h := radicalInSeed_twist_mem m (splitRetractionOfNormal_residue m hN x)
  simpa only [map_mul, map_inv, twist_leviInclusion] using h

/-- The actual binary root radical is normal relative to its split linear seed.
The matrix exchange theorem discharges the positive-root exchange premise. -/
theorem splitRadicalInSeed_normal : (splitRadicalInSeed 0).Normal :=
  splitRadicalInSeed_normal_of_positive_exchanges
    (RadicalCoordinates.rootGenerator_exchange 0)

/-- The unconditional binary retraction onto the actual end-node Levi. -/
def splitRetraction : splitSeed 0 .linear →* splitLevi 0 :=
  splitRetractionOfNormal 0 splitRadicalInSeed_normal

/-- The binary retraction fixes every element of the actual Levi. -/
theorem splitRetraction_levi (l : splitLevi 0) :
    splitRetraction (leviInclusion 0 l) = l :=
  splitRetractionOfNormal_levi 0 splitRadicalInSeed_normal l

/-- The binary retraction has exactly the specified root radical as kernel. -/
theorem splitRetraction_ker : splitRetraction.ker = splitRadicalInSeed 0 :=
  splitRetractionOfNormal_ker 0 splitRadicalInSeed_normal

/-- The binary retraction intertwines the actual seed and Levi twists. -/
theorem splitRetraction_twist (x : splitSeed 0 .linear) :
    splitRetraction (seedTwist 0 x) = leviTwist 0 (splitRetraction x) :=
  splitRetractionOfNormal_twist 0 splitRadicalInSeed_normal x

end ReeF4.Parabolics.BinaryLinear
