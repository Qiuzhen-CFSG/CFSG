module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.FieldAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData

/-!
# Frobenius on the root-defined Ree local subgroups

Squaring coefficients preserves every chosen support of split root generators.
The inclusion of the actual Ree fixed subgroup intertwines its field
automorphism with split Frobenius. Thus the fixed unipotent subgroup, the two
local seeds, and their root radicals are preserved. The Weyl and coroot words
also commute with Frobenius, so the full root Borel and parabolics are preserved.
Finiteness and injectivity turn each containment into equality, without a
simplicity hypothesis.

These equations supply the field part of the local automorphism calculation
used in Aschbacher–Smith F.1.12, printed pp.263–264 of refs/quasithin.pdf.
They concern the subgroups in RootData, not abstract family labels, and do not
assert preservation of those subgroups by arbitrary automorphisms.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms

open LargeLocalSeeds Subgroup Theory.AlgebraicGroup

private theorem frobenius_root_support (m : ℕ) (P : F4Chevalley.Root → Prop) :
    (closure {x | ∃ r t, P r ∧ x = rootGeneratorInGroup m r t}).map
      (splitFrobenius m) ≤ closure {x | ∃ r t, P r ∧ x = rootGeneratorInGroup m r t} := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro x ⟨r, t, hr, rfl⟩
  change splitFrobenius m (rootGeneratorInGroup m r t) ∈
    closure {x | ∃ r t, P r ∧ x = rootGeneratorInGroup m r t}
  rw [splitFrobenius_rootGenerator]
  exact subset_closure ⟨r, t ^ 2, hr, rfl⟩

private theorem fixed_map_eq (m : ℕ) (H : Subgroup (SplitGroup m))
    (hH : H.map (splitFrobenius m) ≤ H) :
    (H.comap (toSplitGroup m)).map (fieldAutomorphism m).toMonoidHom =
      H.comap (toSplitGroup m) := by
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap]
    intro x hx
    change toSplitGroup m (fieldAutomorphism m x) ∈ H
    rw [fieldAutomorphism_coe]
    exact hH (mem_map_of_mem _ hx)
  · exact (card_map_of_injective (fieldAutomorphism m).injective).ge

/-- The concrete field automorphism preserves the fixed positive subgroup. -/
theorem fieldAutomorphism_unipotent (m : ℕ) :
    (unipotent m).map (fieldAutomorphism m).toMonoidHom = unipotent m :=
  fixed_map_eq m (splitUnipotent m) (frobenius_root_support m _)

/-- Both root-defined local seeds are stable under the concrete field action. -/
theorem fieldAutomorphism_seed (m : ℕ) (s : Side) :
    (seed m s).map (fieldAutomorphism m).toMonoidHom = seed m s :=
  fixed_map_eq m (splitSeed m s) (frobenius_root_support m _)

/-- The root radicals are stable independently of identifying them with O₂. -/
theorem fieldAutomorphism_radical (m : ℕ) (s : Side) :
    (radical m s).map (fieldAutomorphism m).toMonoidHom = radical m s :=
  fixed_map_eq m (splitRadical m s) (frobenius_root_support m _)

/-- Frobenius squares the parameter of the actual rank-one Weyl word. -/
theorem splitFrobenius_weylWord (m : ℕ) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    splitFrobenius m (weylWord m r t) = weylWord m r (t ^ 2) := by
  simp only [weylWord, map_mul, splitFrobenius_rootGenerator,
    CharTwo.neg_eq, inv_pow]

/-- Frobenius squares the unit parameter in each coroot word. -/
theorem splitFrobenius_torusWord (m : ℕ) (r : F4Chevalley.Root)
    (t : (CoefficientField m)ˣ) :
    splitFrobenius m (torusWord m r t) = torusWord m r (t ^ 2) := by
  simp only [torusWord, map_mul, splitFrobenius_weylWord, Units.val_pow_eq_pow_val,
    CharTwo.neg_eq, one_pow]

private theorem frobenius_splitTorus (m : ℕ) :
    (splitTorus m).map (splitFrobenius m) ≤ splitTorus m := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro x ⟨r, t, rfl⟩
  change splitFrobenius m (torusWord m r t) ∈ splitTorus m
  rw [splitFrobenius_torusWord]
  exact subset_closure ⟨r, t ^ 2, rfl⟩

/-- The field automorphism preserves the independently defined fixed Borel. -/
theorem fieldAutomorphism_borel (m : ℕ) :
    (borel m).map (fieldAutomorphism m).toMonoidHom = borel m := by
  apply fixed_map_eq m (splitBorel m)
  rw [splitBorel, Subgroup.map_sup]
  exact sup_le_sup (frobenius_root_support m _) (frobenius_splitTorus m)

/-- The full marked parabolics, including their torus, are Frobenius-stable. -/
theorem fieldAutomorphism_parabolic (m : ℕ) (s : Side) :
    (parabolic m s).map (fieldAutomorphism m).toMonoidHom = parabolic m s := by
  apply fixed_map_eq m (splitParabolic m s)
  rw [splitParabolic, Subgroup.map_sup]
  exact sup_le_sup (frobenius_root_support m _) (frobenius_splitTorus m)

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms
