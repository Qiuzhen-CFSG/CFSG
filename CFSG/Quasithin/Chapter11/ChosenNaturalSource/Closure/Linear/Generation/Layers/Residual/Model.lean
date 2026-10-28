module

public import Theory.Representation.SpecialLinearThreeFrameGeometry.DualDisplacements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.ResidualModel

/-!
# Dual action of the original point-parabolic solvable residual

The known point-parabolic residual is the vector stabilizer. Transporting
its standard coordinates places the full point radical in this residual.
The dual shear calculation therefore supplies every functional annihilating
the original point, as an actual additive displacement.

This is the lower counterpart of `parabolic_residual_full`, consumed by
`Layers.Residual` on the literal S₃/S₂ quotient. The residual is solvable,
not the prime-to-two residual of G.2.

Source: Aschbacher--Smith, 11.5.7, printed pp.781--782.
-/

@[expose] public section
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.SpecialLinearGroup
open Matrix.PSL3.PointRadicalGeneration Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {F : Type*} [Field F] [Finite F]

/-- The point radical lies in the full point-parabolic solvable residual. -/
theorem radical_le_parabolic_residual (hF : 4 ≤ Nat.card F)
    (P : Submodule F (Fin 3 → F)) (hP : Module.finrank F P = 1) :
    radical P ≤ residualIn (parabolic P) := by
  obtain ⟨s, rfl⟩ := exists_standardPoint_conjugator P hP
  rw [parabolic_residual_conjugate hF, ← radical_conjugate]
  apply map_mono
  intro a ha
  have hfix := ha.1
  have he := congrFun (hfix ![1,0,0] (by simp [mem_standardPoint]))
  apply (mem_pointLocalSL_iff F a).mpr
  exact ⟨by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using he 0,
    by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using he 1,
    by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using he 2⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {F : Type*} [Field F] [Finite F]

/-- Each functional annihilating the marked point is a residual displacement. -/
theorem exists_parabolic_residual_dual_displacement (hF : 4 ≤ Nat.card F)
    (P : Submodule F (Fin 3 → F)) (hP : Module.finrank F P = 1)
    (f : Module.Dual F (Fin 3 → F)) (hf : f ∈ P.dualAnnihilator) :
    ∃ a ∈ residualIn (parabolic P), ∃ e : Module.Dual F (Fin 3 → F),
      FrameGeometry.natural.dual a e - e = f := by
  have hP0 : P ≠ ⊥ := (Submodule.isAtom_iff_finrank_eq_one.mpr hP).ne_bot
  obtain ⟨a, ha, e, he⟩ :=
    FrameGeometry.exists_pointRadical_dual_displacement P hP0 f hf
  exact ⟨a, radical_le_parabolic_residual hF P hP ⟨ha.2, ha.1⟩, e, he⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
