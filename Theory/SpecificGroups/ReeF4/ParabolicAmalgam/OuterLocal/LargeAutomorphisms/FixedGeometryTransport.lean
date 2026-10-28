module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalStructure

/-!
# Transporting fixed Ree geometry to the canonical matrix carrier

The equivalence from a supplied exceptional-root map to `Model m` preserves
the underlying split matrices. It therefore maps every fixed intersection
with a split subgroup to the corresponding intersection in `Model m`.
In particular, it preserves the positive subgroup's index and transfers
generation by the two fixed seeds.

These are comparison lemmas for the geometric inputs to the automorphism
argument in Aschbacher–Smith F.1.12, printed pp.263–264 of
`refs/quasithin.pdf`. Odd index and fixed-seed generation remain explicit
premises. No simplicity hypothesis or fixed-point generation claim is hidden
in the comparison.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms

open LargeLocalSeeds Subgroup

private theorem modelEquiv_map_intersection {m : ℕ} (d : LocalBlockInput m)
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
    rw [modelEquiv_symm_coe]
    simpa only [Subgroup.mem_comap, toSplitGroup_apply] using hx

/-- The supplied positive fixed subgroup maps to the actual model subgroup. -/
theorem modelEquiv_map_standardUnipotent {m : ℕ} (d : LocalBlockInput m) :
    (standardUnipotent d).map d.modelEquiv.toMonoidHom = unipotent m :=
  modelEquiv_map_intersection d (splitUnipotent m)

/-- Both supplied local seeds map to their corresponding actual model seeds. -/
theorem modelEquiv_map_standardSeed {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    (standardSeed d s).map d.modelEquiv.toMonoidHom = seed m s :=
  modelEquiv_map_intersection d (splitSeed m s)

/-- The positive-subgroup index is unchanged by the matrix-preserving comparison. -/
theorem unipotent_index_eq_standard {m : ℕ} (d : LocalBlockInput m) :
    (unipotent m).index = (standardUnipotent d).index := by
  rw [← modelEquiv_map_standardUnipotent d]
  exact Subgroup.index_map_equiv _ _

/-- A proved odd-index result for a supplied fixed group transfers to `Model m`. -/
theorem unipotent_index_odd_of_standard {m : ℕ} (d : LocalBlockInput m)
    (h : Odd (standardUnipotent d).index) : Odd (unipotent m).index := by
  rwa [unipotent_index_eq_standard d]

/-- Generation by the supplied fixed seeds transfers through their actual images. -/
theorem seed_sup_eq_top_of_standard {m : ℕ} (d : LocalBlockInput m)
    (h : standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤) :
    seed m .suzuki ⊔ seed m .linear = ⊤ := by
  have hmap := congrArg (fun H : Subgroup d.fixedGroup =>
    H.map d.modelEquiv.toMonoidHom) h
  simpa only [Subgroup.map_sup, modelEquiv_map_standardSeed,
    Subgroup.map_top_of_surjective d.modelEquiv.toMonoidHom
      d.modelEquiv.surjective] using hmap

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms
