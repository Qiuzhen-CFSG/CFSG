module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData

/-!
# The end-node Levi in the Ree matrix group

The positive and negative simple root groups at nodes 0 and 3 generate the
split A₁ × A₁ Levi. It lies in the linear seed and is preserved by the Ree
twist. At the binary endpoint the parameter maps are identity, so the twist
exchanges the two pairs of simple root groups without changing parameters.

This specifies the matrix subgroup used by the linear projection. Its product
identification and its complement to the specified radical require further
matrix calculations; neither is included in the definition.

Source: the linear local quotient in Aschbacher–Smith F.1.12(I)(5), printed
pp.263–264 of `refs/quasithin.pdf`, and the standard root Levi construction.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.BinaryLinear

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Subgroup

noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The four signed simple roots on the two end nodes. -/
@[expose] def IsLeviRoot (r : F4Chevalley.Root) : Prop :=
  ∃ i ∈ leviNodes .linear, r = typeF4SimpleRootIndex i ∨ r = -typeF4SimpleRootIndex i

theorem isLeviRoot_isSeedRoot {r : F4Chevalley.Root} (hr : IsLeviRoot r) :
    IsSeedRoot .linear r := by
  rcases hr with ⟨i, hi, rfl | rfl⟩
  · exact Or.inl (typeF4RootPairing_base.isPos_of_mem_support
      (typeF4RootPairing_baseEquiv i).property)
  · exact Or.inr ⟨i, hi, rfl⟩

theorem isLeviRoot_duality {r : F4Chevalley.Root} (hr : IsLeviRoot r) :
    IsLeviRoot (exceptionalRootPermutation r) := by
  rcases hr with ⟨i, hi, rfl | rfl⟩
  · exact ⟨Fin.revPerm i, (rev_mem_leviNodes .linear i).mpr hi,
      Or.inl (exceptionalRootPermutation_simple i)⟩
  · exact ⟨Fin.revPerm i, (rev_mem_leviNodes .linear i).mpr hi,
      Or.inr (exceptionalRootPermutation_neg_simple i)⟩

/-- The actual root-generated split Levi, inside the split F₄ matrices. -/
@[expose] def splitLevi (m : ℕ) : Subgroup (SplitGroup m) :=
  closure {x | ∃ r t, IsLeviRoot r ∧ x = rootGeneratorInGroup m r t}

theorem root_mem_splitLevi (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m)
    (hr : IsLeviRoot r) : rootGeneratorInGroup m r t ∈ splitLevi m :=
  subset_closure ⟨r, t, hr, rfl⟩

theorem splitLevi_le_seed (m : ℕ) : splitLevi m ≤ splitSeed m .linear := by
  apply Subgroup.closure_mono
  rintro x ⟨r, t, hr, rfl⟩
  exact ⟨r, t, isLeviRoot_isSeedRoot hr, rfl⟩

theorem splitLevi_invariant (m : ℕ) :
    (splitLevi m).map (reeAutomorphism m).toMonoidHom = splitLevi m := by
  have h : (splitLevi m).map (reeAutomorphism m).toMonoidHom ≤ splitLevi m := by
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    change reeAutomorphism m (rootGeneratorInGroup m r t) ∈ splitLevi m
    rw [reeAutomorphism_apply, reeTwist_rootGenerator]
    exact root_mem_splitLevi _ _ _ (isLeviRoot_duality hr)
  apply le_antisymm h
  intro x hx
  refine ⟨reeAutomorphism m x, h (mem_map_of_mem _ hx), ?_⟩
  simpa only [MulEquiv.coe_toMonoidHom, reeAutomorphism_apply] using
    reeTwist_involutive m x

/-- The inclusion of the actual Levi in the actual linear seed. -/
@[expose] def leviInclusion (m : ℕ) : splitLevi m →* splitSeed m .linear :=
  inclusion (splitLevi_le_seed m)

/-- The split radical viewed inside the split seed. -/
@[expose] def splitRadicalInSeed (m : ℕ) : Subgroup (splitSeed m .linear) :=
  (splitRadical m .linear).subgroupOf (splitSeed m .linear)

private def restrictTwist (m : ℕ) (H : Subgroup (SplitGroup m))
    (hH : H.map (reeAutomorphism m).toMonoidHom = H) : MulAut H where
  toFun x := ⟨reeAutomorphism m x, hH.le (mem_map_of_mem _ x.property)⟩
  invFun x := ⟨reeAutomorphism m x, hH.le (mem_map_of_mem _ x.property)⟩
  left_inv x := Subtype.ext (by
    simpa only [reeAutomorphism_apply] using reeTwist_involutive m x.val)
  right_inv x := Subtype.ext (by
    simpa only [reeAutomorphism_apply] using reeTwist_involutive m x.val)
  map_mul' x y := Subtype.ext ((reeAutomorphism m).map_mul x.val y.val)

/-- The restriction of the Ree twist to the split linear seed. -/
def seedTwist (m : ℕ) : MulAut (splitSeed m .linear) :=
  restrictTwist m _ (by
    rw [← (canonicalLocalBlockInput m).twist_eq_reeAutomorphism]
    exact splitSeed_twist _ _)

/-- The restriction of the Ree twist to the split end-node Levi. -/
def leviTwist (m : ℕ) : MulAut (splitLevi m) :=
  restrictTwist m _ (splitLevi_invariant m)

@[simp] theorem seedTwist_coe (m : ℕ) (x : splitSeed m .linear) :
    (seedTwist m x).val = reeTwist m x.val := by
  simp only [seedTwist, restrictTwist, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    reeAutomorphism_apply]

@[simp] theorem leviTwist_coe (m : ℕ) (x : splitLevi m) :
    (leviTwist m x).val = reeTwist m x.val := by
  simp only [leviTwist, restrictTwist, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    reeAutomorphism_apply]

/-- Fixed points in the actual split Levi. -/
@[expose] def fixedLevi (m : ℕ) : Subgroup (splitLevi m) :=
  (leviTwist m).toMonoidHom.eqLocus (MonoidHom.id _)

@[simp] theorem mem_fixedLevi (m : ℕ) (x : splitLevi m) :
    x ∈ fixedLevi m ↔ leviTwist m x = x := Iff.rfl

theorem rootFieldEnd_zero (r : F4Chevalley.Root) (t : CoefficientField 0) :
    rootFieldEnd 0 r t = t := by
  classical
  by_cases hr : IsLongRoot r
  · simp [rootFieldEnd, hr]
  · simpa [rootFieldEnd, hr, titsEnd_apply] using field_pow 0 t

/-- The binary twist changes the root but leaves its scalar unchanged. -/
theorem reeTwist_root_zero (r : F4Chevalley.Root) (t : CoefficientField 0) :
    reeTwist 0 (rootGeneratorInGroup 0 r t) =
      rootGeneratorInGroup 0 (exceptionalRootPermutation r) t := by
  rw [reeTwist_rootGenerator, ← rootFieldEnd_apply, rootFieldEnd_zero]

end ReeF4.Parabolics.BinaryLinear
