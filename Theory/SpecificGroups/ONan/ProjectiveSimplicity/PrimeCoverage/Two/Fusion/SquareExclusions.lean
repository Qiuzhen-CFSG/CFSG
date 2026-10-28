module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block0
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block1
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block2
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block3
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block4
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block5
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block6
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.SquareExclusions.Block7

/-!
# Scalar-square exclusions for the O'Nan fusion table

The eight blocks check one nonzero off-diagonal coordinate for each of the 424
indices outside zero and the 87 tree vertices. All witnesses lie in row zero,
in columns 1, 2, or 3. This assembly uses only the numerical matrices and candidate
indices; it does not assume their word evaluations or any group-theoretic result.

Source: `Fusion/MatrixData*.lean`, `Fusion/TreeData.lean`, and the preserved ATLAS
attribution and reproducible data in `Two/source/`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion

private theorem square_covered (i : Fin 512) : SquareExclusions.Covered i := by
  by_cases h0 : i.val < 64
  · have h := SquareExclusions.block0 ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 512) = i := by
      ext
      simp only
      omega
    exact he ▸ h
  by_cases h1 : i.val < 128
  · have h := SquareExclusions.block1 ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 512) = i := by
      ext
      simp only
      omega
    exact he ▸ h
  by_cases h2 : i.val < 192
  · have h := SquareExclusions.block2 ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 512) = i := by
      ext
      simp only
      omega
    exact he ▸ h
  by_cases h3 : i.val < 256
  · have h := SquareExclusions.block3 ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 512) = i := by
      ext
      simp only
      omega
    exact he ▸ h
  by_cases h4 : i.val < 320
  · have h := SquareExclusions.block4 ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 512) = i := by
      ext
      simp only
      omega
    exact he ▸ h
  by_cases h5 : i.val < 384
  · have h := SquareExclusions.block5 ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 512) = i := by
      ext
      simp only
      omega
    exact he ▸ h
  by_cases h6 : i.val < 448
  · have h := SquareExclusions.block6 ⟨i.val - 384, by omega⟩
    have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 512) = i := by
      ext
      simp only
      omega
    exact he ▸ h
  have h := SquareExclusions.block7 ⟨i.val - 448, by omega⟩
  have he : (⟨448 + (i.val - 448), by omega⟩ : Fin 512) = i := by
    ext
    simp only
    omega
  exact he ▸ h

/-- Every noncandidate nonzero index has a square with a nonzero off-diagonal entry. -/
public theorem matrix_square_exclusions : MatrixSquareExclusions := by
  intro i hi hv
  obtain hzero | ⟨t, ht⟩ | hs := square_covered i
  · exact (hi hzero).elim
  · exact (hv t ht).elim
  · exact hs

end ONan.Simplicity.TwoCertificate.Fusion
