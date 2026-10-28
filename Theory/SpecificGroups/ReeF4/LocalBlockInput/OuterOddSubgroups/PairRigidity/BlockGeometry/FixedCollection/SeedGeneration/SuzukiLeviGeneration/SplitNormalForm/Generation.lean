module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm.Exchange

/-!
# Unrestricted Bruhat factors for the full middle-node Levi

The positive four-root block and the two parameter-one simple representatives
generate the signed-root Levi. In particular, the two nonsimple negative
curves are obtained by reflecting the negative simple curves; they are not
omitted from the generation argument. Left word induction and the local cell
exchange then give `U N U` with all three factors in the specified subsystem.

Source: GLS3 1.11.5, 1.12.1, 2.3.5, and Table 2.4 type V,
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Subgroup LargeLocalSeeds BlockParameters.FieldRecovery.SuzukiChart
open PairNormalization.OppositionCell PairNormalization.OppositionCell.FixedBruhatCover
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
namespace SuzukiSplitNormalForm
variable {m : ℕ}

private def cellGenerators (m : ℕ) : Set (SplitGroup m) :=
  (splitSimpleBlock m .suzuki true : Set (SplitGroup m)) ∪
    {x | ∃ i : Fin 4, i ∈ leviNodes .suzuki ∧ x = simpleRep m i}

/-- The nonsimple negative roots are retained: they are simple-reflection
conjugates of the two negative simple root curves. -/
private theorem levi_le_cellGenerators (m : ℕ) :
    splitLevi m .suzuki ≤ closure (cellGenerators m) := by
  let H := closure (cellGenerators m)
  have hp : splitSimpleBlock m .suzuki true ≤ H :=
    fun _ hx => subset_closure (Or.inl hx)
  have hs (i : Fin 4) (hi : i ∈ leviNodes .suzuki) : simpleRep m i ∈ H :=
    subset_closure (Or.inr ⟨i, hi, rfl⟩)
  have hc (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
      (r : F4Chevalley.Root) (t : CoefficientField m)
      (hr : rootGeneratorInGroup m r t ∈ H) :
      rootGeneratorInGroup m
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t ∈ H := by
    rw [← rankOneRepresentative_one_conj_root]
    exact mul_mem (mul_mem (hs i hi) hr) (inv_mem (hs i hi))
  have hn (i : Fin 4) (hi : i ∈ leviNodes .suzuki) (t : CoefficientField m) :
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t ∈ H := by
    rw [← simpleRep_conj_positive]
    exact mul_mem (mul_mem (hs i hi)
      (hp (subset_closure ⟨_, t, isSimpleBlockRoot_simple .suzuki i hi, rfl⟩)))
      (inv_mem (hs i hi))
  apply sup_le hp
  apply (closure_le _).mpr
  rintro _ ⟨r, t, hr, rfl⟩
  obtain ⟨j, hj⟩ := (simpleBlockRoot_iff (-r)).mp
    ((isSimpleBlockRoot_neg_iff .suzuki false r).mpr hr)
  have he : r = -roots j := by rw [← hj, neg_neg]
  rw [he]
  fin_cases j
  · exact hn 1 (by simp [leviNodes]) t
  · exact hn 2 (by simp [leviNodes]) t
  · have h := hc 1 (by simp [leviNodes]) (-typeF4SimpleRootIndex 2) t
      (hn 2 (by simp [leviNodes]) t)
    rw [reflection_neg] at h
    change rootGeneratorInGroup m
      (-(typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1) (typeF4SimpleRootIndex 2))) t ∈ H
    exact h
  · have h := hc 2 (by simp [leviNodes]) (-typeF4SimpleRootIndex 1) t
      (hn 1 (by simp [leviNodes]) t)
    rw [reflection_neg] at h
    change rootGeneratorInGroup m
      (-(typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) (typeF4SimpleRootIndex 1))) t ∈ H
    exact h

/-- Word induction over the positive block and the two simple reflections
covers the actual signed-root Levi by its own unipotent and normalizer factors. -/
theorem unrestricted_factors {g : SplitGroup m} (hg : g ∈ splitLevi m .suzuki) :
    ∃ u ∈ splitSimpleBlock m .suzuki true, ∃ n ∈ splitSuzukiNormalizer m,
      ∃ v ∈ splitSimpleBlock m .suzuki true, g = u * n * v := by
  let F : SplitGroup m → Prop := fun x =>
    ∃ u ∈ splitSimpleBlock m .suzuki true, ∃ n ∈ splitSuzukiNormalizer m,
      ∃ v ∈ splitSimpleBlock m .suzuki true, x = u * n * v
  have hpositive (u : SplitGroup m) (hu : u ∈ splitSimpleBlock m .suzuki true)
      (x : SplitGroup m) (hx : F x) : F (u * x) := by
    obtain ⟨a, ha, n, hn, c, hc, rfl⟩ := hx
    exact ⟨u * a, mul_mem hu ha, n, hn, c, hc, by group⟩
  have hsimple (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
      (x : SplitGroup m) (hx : F x) : F (simpleRep m i * x) := by
    obtain ⟨a, ha, n, hn, c, hc, rfl⟩ := hx
    obtain ⟨b, hb, n', hn', d, hd, he⟩ := simpleRepresentative_cell_exchange i hi ha hn
    refine ⟨b, hb, n', hn', d * c, mul_mem hd hc, ?_⟩
    calc
      _ = (simpleRep m i * a * n) * c := by group
      _ = _ := by rw [he]; group
  have hmem := levi_le_cellGenerators m hg
  clear hg
  change F g
  induction hmem using Subgroup.closure_induction_left with
  | one => exact ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | ⟨i, hi, rfl⟩
    · exact hpositive x hx y ih
    · exact hsimple i hi y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | ⟨i, hi, rfl⟩
    · exact hpositive x⁻¹ (inv_mem hx) y ih
    · rw [simpleRep_inv]
      exact hsimple i hi y ih

end SuzukiSplitNormalForm
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
