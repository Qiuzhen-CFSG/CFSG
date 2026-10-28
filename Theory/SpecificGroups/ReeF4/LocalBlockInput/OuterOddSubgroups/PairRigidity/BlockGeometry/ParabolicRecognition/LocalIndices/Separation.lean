module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.RootIntersection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction.Grading

/-!
# Separation of the negative Ree blocks from the root Borel

The positive Suzuki block lies in the linear radical, while the positive
linear block lies in its Levi complement. Their disjointness transports to
the negative blocks by the proved opposition action. The two root-parabolic
intersection identities then force the intersection of the negative
unipotent group and the root Borel into both disjoint blocks.

This proves block–Borel separation from the torus identity alone; neither
local coset coverage nor an identification of an intrinsic normalizer is
assumed.

Source: GLS3, Theorems 2.3.8(c,d) and 2.6.5(g),
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open Subgroup LargeLocalSeeds
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open BlockParameters.FieldRecovery
variable {m : ℕ}

private theorem suzuki_positive_root_radical {r : F4Chevalley.Root}
    (hr : IsSimpleBlockRoot .suzuki true r) : IsRadicalRoot .linear r := by
  refine ⟨hr.2, ?_⟩
  by_cases h1 : typeF4SimpleCoefficient r.val 1 = 0
  · by_cases h2 : typeF4SimpleCoefficient r.val 2 = 0
    · have h0 := hr.1 0 (by simp [leviNodes])
      have h3 := hr.1 3 (by simp [leviNodes])
      exfalso
      apply typeF4RootPairing.ne_zero r
      change r.val = 0
      simp only [typeF4SimpleCoefficient] at h0 h1 h2 h3
      ext i
      fin_cases i
      · change r.val 0 = 0
        linarith
      · change r.val 1 = 0
        linarith
      · change r.val 2 = 0
        linarith
      · change r.val 3 = 0
        linarith
    · exact ⟨2, by simp [leviNodes], h2⟩
  · exact ⟨1, by simp [leviNodes], h1⟩

private theorem splitSuzukiBlock_le_linearRadical :
    splitSimpleBlock m .suzuki true ≤ splitRadical m .linear := by
  apply Subgroup.closure_mono
  rintro x ⟨r, t, hr, rfl⟩
  exact ⟨r, t, suzuki_positive_root_radical hr, rfl⟩

private theorem splitLinearBlock_le_linearLevi :
    splitSimpleBlock m .linear true ≤ Parabolics.BinaryLinear.splitLevi m := by
  apply Subgroup.closure_mono
  rintro x ⟨r, t, hr, rfl⟩
  exact ⟨r, t, Parabolics.BinaryLinear.isLeviRoot_of_middle_coefficients_zero r
    (hr.1 1 (by simp [leviNodes])) (hr.1 2 (by simp [leviNodes])), rfl⟩

/-- The two fixed simple blocks of either sign have trivial intersection. -/
theorem simpleBlocks_disjoint (d : LocalBlockInput m) (positive : Bool) :
    Disjoint (simpleBlock d .suzuki positive) (simpleBlock d .linear positive) := by
  have hp : Disjoint (simpleBlock d .suzuki true) (simpleBlock d .linear true) := by
    have hsplit := (Parabolics.BinaryLinear.splitRadical_disjoint_splitLevi m).mono
      splitSuzukiBlock_le_linearRadical splitLinearBlock_le_linearLevi
    apply Subgroup.disjoint_def.mpr
    intro x hx hy
    exact Subtype.ext (Subgroup.disjoint_def.mp hsplit hx hy)
  cases positive
  · simpa only [opposition_map_simpleBlock] using
      Subgroup.disjoint_map
        (f := (MulAut.conj (PairNormalization.opposition d)).toMonoidHom)
        (MulAut.conj (PairNormalization.opposition d)).injective hp
  · exact hp

/-- Opposite unipotence and positive Borel membership force the identity. -/
theorem oppositeUnipotent_disjoint_rootBorel (d : LocalBlockInput m)
    (hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m) :
    Disjoint (oppositeUnipotent d) (rootBorel d) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hB
  have hs (s : Side) : x ∈ simpleBlock d s false := by
    rw [← oppositeUnipotent_inf_rootBorel_sup_simpleBlock d hT s]
    exact ⟨hx, (le_sup_left : rootBorel d ≤ rootBorel d ⊔ simpleBlock d s false) hB⟩
  exact Subgroup.disjoint_def.mp (simpleBlocks_disjoint d false) (hs .suzuki) (hs .linear)

/-- Each negative block meets the positive root Borel trivially. -/
theorem negativeBlock_disjoint_rootBorel (d : LocalBlockInput m)
    (hT : Parabolics.splitTorus m = Parabolics.diagonalTorus m) (s : Side) :
    Disjoint (simpleBlock d s false) (rootBorel d) :=
  (oppositeUnipotent_disjoint_rootBorel d hT).mono_left (simpleBlock_negative_le d s)

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
