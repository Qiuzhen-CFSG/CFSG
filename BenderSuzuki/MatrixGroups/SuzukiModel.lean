module

public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.Comparator.Defs

/-!
# The shared Suzuki model

The shared `SzModel` and the concrete Suzuki matrix subgroup have identical
generators. Equality of their generating sets identifies their subgroup
closures, giving the model bridge independently of the classification theorem.

Source: the explicit Suzuki matrix definitions in the imported modules.
-/

open Matrix BenderSuzuki.MatrixGroups

/-- The explicit final-theorem Suzuki model is the repository's standard Suzuki matrix group. -/
public theorem szModel_eq_suzukiMatrixGroup (n : ℕ) :
    SzModel n = BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n := by
  apply congrArg Subgroup.closure
  ext A
  simp only [SzGenerators,
    BenderSuzuki.MatrixGroups.SuzukiMatrixGeneratorSet,
    Set.mem_ofPred_eq]
  constructor
  · rintro (⟨a, b, hA⟩ | ⟨x, hA⟩ | hA)
    · left
      refine ⟨a, b, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simpa [BenderSuzuki.MatrixGroups.SuzukiRootGL,
        BenderSuzuki.MatrixGroups.SuzukiRootMatrix] using
        congrArg (fun M ↦ M i j) hA
    · right
      left
      refine ⟨x, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simpa [BenderSuzuki.MatrixGroups.SuzukiTorusGL,
        BenderSuzuki.MatrixGroups.SuzukiTorusMatrix] using
        congrArg (fun M ↦ M i j) hA
    · right
      right
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simpa [BenderSuzuki.MatrixGroups.SuzukiWeylGL,
        BenderSuzuki.MatrixGroups.SuzukiWeylMatrix] using
        congrArg (fun M ↦ M i j) hA
  · rintro (⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl)
    · left
      exact ⟨a, b, by
        simp [BenderSuzuki.MatrixGroups.SuzukiRootGL,
          BenderSuzuki.MatrixGroups.SuzukiRootMatrix]⟩
    · right
      left
      exact ⟨x, by
        simp [BenderSuzuki.MatrixGroups.SuzukiTorusGL,
          BenderSuzuki.MatrixGroups.SuzukiTorusMatrix]⟩
    · right
      right
      simp [BenderSuzuki.MatrixGroups.SuzukiWeylGL,
        BenderSuzuki.MatrixGroups.SuzukiWeylMatrix]

