module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.RootFactors
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Normality
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.BorelGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.BorelGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.Normalization
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Normalization


/-!
# Borel factorization at a simple relative root

The existing fixed positive-factor theorems give generation by the simple
block and the prescribed radical. Relative normality in the split seed,
restricted to its fixed subgroup, turns this join into an actual product
with the radical first. The fixed Borel decomposition then writes every
Borel element as a fixed torus factor, a fixed radical factor and a simple
positive-block factor. The concrete relative reflection conjugates the
first two factors into the Borel.

All fields and both sides are covered, with the full middle B₂ block and
full fixed torus. No normalizer-word hypothesis is used.
Source: GLS3 2.3.4(c), 2.3.7–8 and §2.4, Table 2.4 types V and VI,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Subgroup LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open LocalBlockInput.PairRigidity.LocalIndices
open Theory.AlgebraicGroup.StandardRootSystem
open scoped Pointwise

private theorem relativeWeyl_linear (m : ℕ) (d : LocalBlockInput m) :
    relativeWeyl d .linear = linearPanelWeyl d 1 := by
  apply Subtype.ext
  rw [relativeWeyl_val, linearPanelWeyl_split]
  simp [simpleWord, sideWord]

private theorem local_unipotent_factors {m : ℕ} (d : LocalBlockInput m)
    (s : Side) (u : d.fixedGroup) (hu : u ∈ standardUnipotent d) :
    ∃ r ∈ standardRadical d s, ∃ x ∈ simpleBlock d s true, u = r * x := by
  have hgen : standardUnipotent d ≤ simpleBlock d s true ⊔ standardRadical d s := by
    cases s with
    | linear => exact standardUnipotent_le_linearBlock_sup_radical d
    | suzuki => exact standardUnipotent_le_suzukiBlock_sup_radical d
  have hnorm : simpleBlock d s true ≤ normalizer (standardRadical d s) := by
    have h := (simpleBlock_positive_le d s).trans (standardUnipotent_le_seed d s)
    exact (h.trans (comap_mono (splitSeed_le_radical_normalizer m s))).trans
      (le_normalizer_comap d.fixedGroup.subtype)
  have hm : u ∈ (standardRadical d s : Set d.fixedGroup) * (simpleBlock d s true : Set d.fixedGroup) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm, sup_comm]
    exact hgen hu
  obtain ⟨r, hr, x, hx, he⟩ := hm
  exact ⟨r, hr, x, hx, he.symm⟩

private theorem local_borel_factors {m : ℕ} (d : LocalBlockInput m)
    (s : Side) (b : d.fixedGroup) (hb : b ∈ rootBorel d) :
    ∃ b₀ ∈ rootBorel d, ∃ x ∈ simpleBlock d s true,
      b = b₀ * x ∧ relativeWeyl d s * b₀ * (relativeWeyl d s)⁻¹ ∈ rootBorel d := by
  let T := (splitTorus m).subgroupOf d.fixedGroup
  have hnorm : T ≤ normalizer (standardUnipotent d) :=
    (comap_mono (splitTorus_normalizes_unipotent m)).trans
      (le_normalizer_comap d.fixedGroup.subtype)
  have hprod : b ∈ (T : Set d.fixedGroup) * (standardUnipotent d : Set d.fixedGroup) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm, sup_comm]
    rw [rootBorel_eq_standardUnipotent_sup_linearPanelTorus d (splitTorus_eq_diagonalTorus m)] at hb
    exact hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hprod
  obtain ⟨r, hr, x, hx, rfl⟩ := local_unipotent_factors d s u hu
  have htB : t ∈ rootBorel d := linearPanelTorus_le_borel d ht
  have hrB : r ∈ rootBorel d :=
    show r.val ∈ splitBorel m from
      (le_sup_left : splitUnipotent m ≤ splitBorel m) (standardRadical_le_unipotent d s hr)
  refine ⟨t * r, mul_mem htB hrB, x, hx, (mul_assoc _ _ _).symm, ?_⟩
  have hT : relativeWeyl d s * t * (relativeWeyl d s)⁻¹ ∈ rootBorel d := by
    cases s with
    | linear =>
      rw [relativeWeyl_linear]
      exact linearPanelTorus_le_borel_comap_weyl d ht
    | suzuki => exact suzukiPanelTorus_le_borel_comap_weyl d ht
  have hR : relativeWeyl d s * r * (relativeWeyl d s)⁻¹ ∈ rootBorel d := by
    cases s with
    | linear =>
      rw [relativeWeyl_linear]
      exact linearPanelRadical_le_borel_comap_weyl d hr
    | suzuki => exact suzukiPanelRadical_le_borel_comap_weyl d hr
  convert (rootBorel d).mul_mem hT hR using 1
  group

/-- The complete fixed Borel factors with its simple positive relative block last. -/
theorem borelSimpleFactorization (m : ℕ) : BorelSimpleFactorization m := by
  intro s b hb
  let d := canonicalLocalBlockInput m
  have hB (x : d.fixedGroup) : d.modelEquiv x ∈ borel m ↔ x ∈ rootBorel d := by
    rw [← rootBorel_map_modelEquiv d]
    exact mem_map_iff_mem d.modelEquiv.injective
  have hb' : d.modelEquiv.symm b ∈ rootBorel d :=
    (hB _).mp (by simpa only [MulEquiv.apply_symm_apply] using hb)
  obtain ⟨b₀, hb₀, x, hx, he, hc⟩ := local_borel_factors d s _ hb'
  refine ⟨d.modelEquiv b₀, (hB b₀).mpr hb₀, d.modelEquiv x,
    (modelEquiv_mem_relativePositiveBlock_iff d s x).mpr hx, ?_, ?_⟩
  · simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg d.modelEquiv he
  · have hh := (hB _).mpr hc
    rw [map_mul, map_mul, map_inv, wordExchange_modelEquiv_relativeWeyl] at hh
    have hv : (weylLift m s)⁻¹ = weylLift m s := by
      exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weylLift_sq m s)
    simpa only [hv] using hh

end ReeF4.SectionGeometry.BNPair
