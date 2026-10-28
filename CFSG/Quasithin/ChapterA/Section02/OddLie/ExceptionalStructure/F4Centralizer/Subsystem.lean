module

public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer
public import Theory.SpecificGroups.LieType.F4RootCentralizer

/-!
# Applying a faithful orthogonal-root realization to the source rank bound

A faithful symplectic homomorphism into the F4 elementary matrix group,
with the specified root-subgroup range and scalar involution, gives a
faithful map into the literal residual centralizer once commutation with
the fundamental SL2 is established. The rank-three elementary subgroup
already proved in Sp6 then contradicts the source bound m3 ≤ 1.

This application needs no upper bound on the centralizer. The independent
residual exhaustion remains necessary for the full Sp6 equivalence, owned
by `Theory.SpecificGroups.LieType.F4RootCentralizer`. The lattice realization
and commutation inputs below remain explicit; this is not the unconditional
F4 exclusion in Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer
open ExceptionalSplit
open ExceptionalSplit.F4RootSL2 ExceptionalSplit.F4RootCentralizer
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]

/-- The concrete faithful lattice realization discharges the embedding premise
of the existing source rank obstruction, without a residual exhaustion premise. -/
theorem source_bound_contradiction_of_faithful_subsystem
    (p : ℕ) [CharP F p] (hF : (2 : F) ≠ 0)
    (f : Matrix.symplecticGroup (Fin 3) F →* Elementary F)
    (hrange : f.range = elementaryComplement F)
    (hinj : Function.Injective f)
    (hneg : f symplecticNegOne = elementaryHom (-1 : SL(2, F)))
    (hcomm : projectedComplement F ≤ Centralizer F)
    (hbound : primeRank 3 (Residual p F) ≤ 1) : False := by
  exact source_bound_contradiction p fundamentalRoot hbound
    (symplecticToResidual p f hrange hcomm)
    (symplecticToResidual_injective p f hrange hcomm
      (central_kernel_of_faithful_neg_one hF f hinj hneg))

end CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer
end
