module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration.SuzukiWitness.MatrixSeparation


/-!
# A positive Ree element whose square survives the Suzuki radical

The middle-node word `x_α(1) x_β(1) x_(α+β)(1)` is fixed by the actual
Ree twist under the explicit `B2RootSwap` matrix relation. Its square is
`x_(α+β)(1) x_(α+2β)(1)`. A nonzero Cartan-column entry, together with the
outer-coefficient grading of radical matrices, keeps that square outside
the root-defined Suzuki radical. All other inputs are proved here or in
the imported root-matrix lemmas, for every m including m = 0.

This conditional calculation supplies the square witness used in positive
normal generation of the fixed Suzuki seed. The caller must discharge
`B2RootSwap`; no projection, residual equality, or ambient simplicity is
assumed. The group at m = 0 is the full binary Ree group.

Source: the middle-node Levi calculation underlying Aschbacher–Smith,
F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section

namespace ReeF4.Parabolics.SeedGeneration
open RadicalCoordinates.FixedCoordinates LargeLocalSeeds SuzukiWitness
noncomputable section

/-- Assuming the B₂ matrix swap, a positive Ree element has square outside
its Suzuki radical, over every coefficient field including the binary field. -/
theorem exists_unipotent_square_not_mem_suzuki_radical (m : ℕ) (hswap : B2RootSwap m) :
    ∃ x ∈ unipotent m, x ^ 2 ∉ radical m .suzuki := by
  let x : Model m := ⟨positiveWord m, (mem_fixedSubgroup m _).mpr (positiveWord_fixed m hswap)⟩
  refine ⟨x, ?_, ?_⟩
  · change toSplitGroup m x ∈ splitUnipotent m
    rw [toSplitGroup_apply]
    exact positiveWord_mem_unipotent m
  · intro h
    have hr : toSplitGroup m (x ^ 2) ∈ splitRadical m .suzuki := h
    rw [map_pow, toSplitGroup_apply] at hr
    change positiveWord m ^ 2 ∈ splitRadical m .suzuki at hr
    rw [positiveWord_sq m hswap] at hr
    exact centralWord_not_mem_radical m hr

end
end ReeF4.Parabolics.SeedGeneration
