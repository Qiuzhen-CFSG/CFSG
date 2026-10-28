module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.BlockCollection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization

/-!
# The fixed coroot torus normalizes all eight Ree blocks

Diagonal conjugation preserves the split-root support of each paired or B₂
block. A conjugate of a fixed element is still fixed. Injectivity of the
split block coordinates therefore forces the individual pair or quartet
parameters to satisfy their twist equations. Their established solutions
place the conjugate in the original generated root subgroup Xᵢ.

This proves normalization of the entire block, including the nonabelian
B₂ law, without assuming a scalar formula for the folded main curve. Direct
conjugation uses the inverse torus character in the split root convention.
No central-extension or multiplier assumption enters this calculation.

Source: GLS3 §§2.3–2.4, Table 2.4 and 2.4.5(d); the covering application is
Aschbacher–Smith I.1.1–4, printed pp.407–408.
-/

public section
noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary
open Subgroup
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics LargeLocalSeeds Parabolics.RadicalCoordinates
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open NormalizedRootCentralizers.CenterExponent
open ElementaryTwoBound ElementaryTwoBound.RootCalculations

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem pairWord_injective (m : ℕ) (B : RootBlocks .positive) (j : Fin (pairCount .positive)) :
    Function.Injective (pairWord m (fun k => (B.roots (.inl (j,k))).val)) := by
  classical
  let pack (t : Fin 2 → CoefficientField m) : BlockParameters m .positive :=
    (fun i => if i = j then t else fun _ => 0, fun _ _ => 0)
  have hw (t : Fin 2 → CoefficientField m) :
      B.blockWord m (pack t) = pairWord m (fun k => (B.roots (.inl (j,k))).val) t := by
    fin_cases j <;> simp [RootBlocks.blockWord, pack, pairCount, quartetCount,
      List.ofFn_succ, pairWord, quartetWord, root_zero]
  intro t u h
  have hp := B.blockWord_injective m (wordInSubgroup_bijective m B.order)
    ((hw t).trans (h.trans (hw u).symm))
  simpa [pack] using congrArg (fun p => p.1 j) hp

private theorem quartetWord_injective (m : ℕ) (B : RootBlocks .positive) (j : Fin (quartetCount .positive)) :
    Function.Injective (quartetWord m (fun k => (B.roots (.inr (j,k))).val)) := by
  classical
  let pack (t : Fin 4 → CoefficientField m) : BlockParameters m .positive :=
    (fun _ _ => 0, fun i => if i = j then t else fun _ => 0)
  have hw (t : Fin 4 → CoefficientField m) :
      B.blockWord m (pack t) = quartetWord m (fun k => (B.roots (.inr (j,k))).val) t := by
    fin_cases j <;> simp [RootBlocks.blockWord, pack, pairCount, quartetCount,
      List.ofFn_succ, pairWord, quartetWord, root_zero]
  intro t u h
  have hp := B.blockWord_injective m (wordInSubgroup_bijective m B.order)
    ((hw t).trans (h.trans (hw u).symm))
  simpa [pack] using congrArg (fun p => p.2 j) hp

private theorem fixed_pair_mem_X (m : ℕ) (j : Fin (pairCount .positive)) (x : Model m)
    (t : Fin 2 → CoefficientField m)
    (hx : toSplitGroup m x = pairWord m
      (fun k => (positiveRootWordLayout.blocks.roots (.inl (j,k))).val) t) :
    x ∈ X m (positiveRootWordLayout.pairIndex j) := by
  have hf : reeTwist m (toSplitGroup m x) = toSplitGroup m x := by
    simpa only [toSplitGroup_apply, mem_fixedSubgroup, reeAutomorphism_apply] using x.property
  rw [hx, positiveRootWordLayout.blocks.twist_pair m (mixedRootCommutation m)] at hf
  have ht := (pairTwist_fixed_iff m t).mp
    (pairWord_injective m positiveRootWordLayout.blocks j hf)
  apply (mem_X_iff m _ (positiveRootWordLayout.pair_odd j) x).mpr
  refine ⟨t 0, ?_⟩
  apply toSplitGroup_injective m
  rw [mainElement_coe, positiveRootWordLayout.pair_rootWord, hx]
  exact congrArg (pairWord m _) ht.symm

private theorem fixed_quartet_mem_X (m : ℕ) (j : Fin (quartetCount .positive)) (x : Model m)
    (t : Fin 4 → CoefficientField m)
    (hx : toSplitGroup m x = quartetWord m
      (fun k => (positiveRootWordLayout.blocks.roots (.inr (j,k))).val) t) :
    x ∈ X m (positiveRootWordLayout.quartetIndex j) := by
  have hf : reeTwist m (toSplitGroup m x) = toSplitGroup m x := by
    simpa only [toSplitGroup_apply, mem_fixedSubgroup, reeAutomorphism_apply] using x.property
  rw [hx, positiveRootWordLayout.blocks.twist_quartet m (mixedRootCommutation m)
    (b2RootSwap m)] at hf
  have ht := (quartetTwist_fixed_iff m t).mp
    (quartetWord_injective m positiveRootWordLayout.blocks j hf)
  apply (mem_X_even m _ (positiveRootWordLayout.quartet_even j) x).mpr
  refine ⟨t 0, titsEnd m (t 2) + t 0 * titsEnd m (t 0), ?_⟩
  apply toSplitGroup_injective m
  rw [blockPoint, map_mul, mainElement_coe, centralElement_coe, hx,
    ← positiveRootWordLayout.quartet_factorization m (mixedRootCommutation m)]
  exact congrArg (quartetWord m _) ht.symm

private def directScale (m : ℕ) (u : TorusParameter m) (r : F4Chevalley.Root) :
    CoefficientField m :=
  (RootPairing.IntegralGeckConstruction.integralChevalleyRootScale
    (P := typeF4RootPairing) u⁻¹ r : (CoefficientField m)ˣ)

private theorem diagonal_conj_root (m : ℕ) (u : TorusParameter m)
    (z : SplitGroup m) (hz : z.val = diagonalTorusHom m u)
    (r : F4Chevalley.Root) (a : CoefficientField m) :
    (MulAut.conj z) (rootGeneratorInGroup m r a) =
      rootGeneratorInGroup m r (directScale m u r * a) := by
  apply Subtype.ext
  change z.val * F4Chevalley.rootCurve r a * z.val⁻¹ = _
  rw [hz]
  have he := F4Chevalley.rootCurve_torus_conjugation u⁻¹ r a
  simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe,
    directScale] using he

private theorem diagonal_conj_pair (m : ℕ) (u : TorusParameter m)
    (z : SplitGroup m) (hz : z.val = diagonalTorusHom m u)
    (r : Fin 2 → F4Chevalley.Root) (a : Fin 2 → CoefficientField m) :
    (MulAut.conj z) (pairWord m r a) =
      pairWord m r (fun k => directScale m u (r k) * a k) := by
  simp only [pairWord, map_mul, diagonal_conj_root m u z hz]

private theorem diagonal_conj_quartet (m : ℕ) (u : TorusParameter m)
    (z : SplitGroup m) (hz : z.val = diagonalTorusHom m u)
    (r : Fin 4 → F4Chevalley.Root) (a : Fin 4 → CoefficientField m) :
    (MulAut.conj z) (quartetWord m r a) =
      quartetWord m r (fun k => directScale m u (r k) * a k) := by
  simp only [quartetWord, map_mul, diagonal_conj_root m u z hz]

/-- Every literal fixed coroot element normalizes each full positive block. -/
theorem fixedTorus_normalizes_X (m : ℕ) (i : Fin 8) :
    fixedTorus m ≤ normalizer (X m i : Set (Model m)) := by
  rw [le_normalizer_iff]
  intro z hz x hx
  have hzt : toSplitGroup m z ∈ diagonalTorus m := by
    rw [← splitTorus_eq_diagonalTorus m]
    exact hz
  obtain ⟨u,hu⟩ := hzt
  have hu' : (toSplitGroup m z).val = diagonalTorusHom m u := hu.symm
  change (MulAut.conj z) x ∈ X m i
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    rcases positiveRootWordLayout.positive_covers i with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · apply fixed_pair_mem_X m j _
        (fun k => directScale m u (positiveRootWordLayout.blocks.roots (.inl (j,k))).val *
          pairSolution m a k)
      simp only [MulAut.conj_apply, map_mul, map_inv]
      rw [mainElement_coe, positiveRootWordLayout.pair_rootWord]
      exact diagonal_conj_pair m u _ hu' _ _
    · apply fixed_quartet_mem_X m j _
        (fun k => directScale m u (positiveRootWordLayout.blocks.roots (.inr (j,k))).val *
          quartetSolution m a (a * halfFrobenius m a) k)
      simp only [MulAut.conj_apply, map_mul, map_inv]
      rw [mainElement_coe, positiveRootWordLayout.quartet_rootWord]
      exact diagonal_conj_quartet m u _ hu' _ _
  | one => simpa only [map_one] using (one_mem (X m i))
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using inv_mem hx

end ReeF4.CentralCovers.TwoPrimary
