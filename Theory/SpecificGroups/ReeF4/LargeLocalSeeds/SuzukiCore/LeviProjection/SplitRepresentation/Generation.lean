module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.FixedDescent
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates.SplitBlock
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm.Geometry

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.NegativeSimple.Reflection

/-!
# Signed simple generators of the whole split B₂ Levi

The four signed simple curves generate both complete root blocks. Each of
the two nonsimple positive roots is a simple reflection of the other simple
root; the same conjugation supplies its negative. Thus this generation result
concerns the full root-defined Levi, not only a subgroup of simple curves.

Source: GLS3 §§1.12 and 2.3; the B₂ Levi underlying Aschbacher–Smith
F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section
namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LocalBlockInput.PairRigidity
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiChart
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

/-- Each signed simple curve lies in the actual full Levi. -/
theorem signedRoot_mem (i : Fin 4) (t : CoefficientField m) :
    rootGeneratorInGroup m (signedRoot i) t ∈ splitLevi m .suzuki := by
  fin_cases i
  · exact mem_sup_left (subset_closure
      ⟨_, t, isSimpleBlockRoot_simple .suzuki 1 (by simp [leviNodes]), rfl⟩)
  · exact mem_sup_left (subset_closure
      ⟨_, t, isSimpleBlockRoot_simple .suzuki 2 (by simp [leviNodes]), rfl⟩)
  · exact mem_sup_right (subset_closure
      ⟨_, t, isSimpleBlockRoot_neg_simple .suzuki 1 (by simp [leviNodes]), rfl⟩)
  · exact mem_sup_right (subset_closure
      ⟨_, t, isSimpleBlockRoot_neg_simple .suzuki 2 (by simp [leviNodes]), rfl⟩)

/-- Generation includes both nonsimple roots and their negatives. -/
theorem signedRoot_closure (m : ℕ) :
    closure (Set.range (fun a : Fin 4 × CoefficientField m =>
      rootGeneratorInGroup m (signedRoot a.1) a.2)) = splitLevi m .suzuki := by
  let H := closure (Set.range (fun a : Fin 4 × CoefficientField m =>
    rootGeneratorInGroup m (signedRoot a.1) a.2))
  have hs (i : Fin 4) (t : CoefficientField m) :
      rootGeneratorInGroup m (signedRoot i) t ∈ H := subset_closure ⟨(i,t), rfl⟩
  have hp (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (t : CoefficientField m) :
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) t ∈ H := by
    rcases hi with rfl | rfl
    · exact hs 0 t
    · exact hs 1 t
  have hn (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (t : CoefficientField m) :
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t ∈ H := by
    rcases hi with rfl | rfl
    · exact hs 2 t
    · exact hs 3 t
  have hw (i : Fin 4) (hi : i ∈ leviNodes .suzuki) :
      rankOneRepresentative m (typeF4SimpleRootIndex i) 1 ∈ H :=
    mul_mem (mul_mem (hp i hi _) (hn i hi _)) (hp i hi _)
  have hc (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
      (r : F4Chevalley.Root) (t : CoefficientField m)
      (hr : rootGeneratorInGroup m r t ∈ H) :
      rootGeneratorInGroup m
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t ∈ H := by
    rw [← rankOneRepresentative_one_conj_root]
    exact mul_mem (mul_mem (hw i hi) hr) (inv_mem (hw i hi))
  have hall (p : Bool) : splitSimpleBlock m .suzuki p ≤ H := by
    apply (closure_le _).mpr
    rintro _ ⟨r,t,hr,rfl⟩
    cases p
    · obtain ⟨j,hj⟩ := (simpleBlockRoot_iff (-r)).mp
        ((isSimpleBlockRoot_neg_iff .suzuki false r).mpr hr)
      have he : r = -roots j := by rw [← hj, neg_neg]
      rw [he]
      fin_cases j
      · exact hn 1 (by simp [leviNodes]) t
      · exact hn 2 (by simp [leviNodes]) t
      · have h := hc 1 (by simp [leviNodes]) (-typeF4SimpleRootIndex 2) t
          (hn 2 (by simp [leviNodes]) t)
        rw [SuzukiSplitNormalForm.reflection_neg] at h
        exact h
      · have h := hc 2 (by simp [leviNodes]) (-typeF4SimpleRootIndex 1) t
          (hn 1 (by simp [leviNodes]) t)
        rw [SuzukiSplitNormalForm.reflection_neg] at h
        exact h
    · obtain ⟨j,rfl⟩ := (simpleBlockRoot_iff r).mp hr
      fin_cases j
      · exact hp 1 (by simp [leviNodes]) t
      · exact hp 2 (by simp [leviNodes]) t
      · exact hc 1 (by simp [leviNodes]) _ t (hp 2 (by simp [leviNodes]) t)
      · exact hc 2 (by simp [leviNodes]) _ t (hp 1 (by simp [leviNodes]) t)
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨⟨i,t⟩,rfl⟩
    exact signedRoot_mem i t
  · exact sup_le (hall true) (hall false)

/-- The signed simple generators as elements of the whole Levi. -/
def splitGenerator (m : ℕ) (a : Fin 4 × CoefficientField m) : splitLevi m .suzuki :=
  ⟨rootGeneratorInGroup m (signedRoot a.1) a.2, signedRoot_mem a.1 a.2⟩

/-- Internal generation, for induction on arbitrary elements of the Levi. -/
theorem splitGenerator_closure (m : ℕ) :
    closure (Set.range (splitGenerator m)) = ⊤ := by
  apply Subgroup.map_injective (splitLevi m .suzuki).subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  change closure (Set.range (fun a : Fin 4 × CoefficientField m =>
    rootGeneratorInGroup m (signedRoot a.1) a.2)) = _
  rw [signedRoot_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The restricted twist has precisely the prescribed root and parameter action. -/
theorem splitTwist_generator (d : LocalBlockInput m) (a : Fin 4 × CoefficientField m) :
    splitTwist d (splitGenerator m a) =
      splitGenerator m (swapIndex a.1, twistParameter m a.1 a.2) := by
  apply Subtype.ext
  change d.twist (rootGeneratorInGroup m (signedRoot a.1) a.2) = _
  rw [d.twist_root, exceptionalRootPermutation_signedRoot]
  rfl

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
