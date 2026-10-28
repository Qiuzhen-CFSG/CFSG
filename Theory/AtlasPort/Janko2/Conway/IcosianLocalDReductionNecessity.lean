/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalDReductionNecessity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalDReductionTest
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalCScalarNecessity

/-!
# IcosianLocalDReductionNecessity

Fixing the shape-D reference line forces the prescribed permutation and reduction
constraints. Its distinct nonzero coordinates determine these restrictions.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalDReductionNecessity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

theorem icosianLocalDRoot_word_injective :
    Function.Injective (icosianRootNormWord icosianLocalDRoot) := by
  rw [icosianLocalDRoot_norm_word]
  decide +kernel

theorem icosianLocalDRoot_nonzero (i : Fin 3) : icosianLocalDRoot.val i≠0 := by
  intro hz
  have hn : icosianRootNormWord icosianLocalDRoot i=0 :=
    icosianRootNormWord_of_norm _ _ 0 (by simp [hz,icosianNorm])
  rw [icosianLocalDRoot_norm_word] at hn
  have hne : ∀ j : Fin 3,(![((1-QuadraticAlgebra.omega)^2 : GoldenInteger),
      QuadraticAlgebra.omega^2,1] j)≠0 := by decide +kernel
  exact hne i hn

theorem icosianLocalDLine_permutation (g : icosianLiftedMonomial)
    (h : icosianMonomialToHermitian g • icosianRootPoint icosianLocalDRoot=
      icosianRootPoint icosianLocalDRoot) : g.val.right=1 := by
  have he : g.val.right.symm=1 := by
    apply Equiv.ext
    intro i
    exact icosianLocalDRoot_word_injective
      (icosianMonomial_line_permutation_norm g icosianLocalDRoot h i)
  exact congrArg Equiv.symm he

theorem icosianLocalDLine_reduction_test (g : icosianLiftedMonomial)
    (hp : g.val.right=1) (u : icosianNormOneGroup)
    (hu : ∀ i,(g.val.left i).val.val*(icosianLocalDRoot.val (g.val.right.symm i)).val=
      (icosianLocalDRoot.val i).val*u.val.val) :
    IcosianLocalDReductionTest (icosianNormOneReduction u) := by
  have hc (i : Fin 3) : icosianLocalDMatrixConjugate (icosianNormOneReduction u) i=
      (icosianNormOneReduction (g.val.left i) : IcosianMatrix) := by
    have he : icosianNormOneToOrder (g.val.left i)*icosianLocalDRoot.val i=
        icosianLocalDRoot.val i*icosianNormOneToOrder u := by
      apply Subtype.ext
      have hpi : g.val.right.symm i=i := by rw [hp]; rfl
      change (g.val.left i).val.val*(icosianLocalDRoot.val i).val=
        (icosianLocalDRoot.val i).val*u.val.val
      simpa only [hpi] using hu i
    have hm := congrArg icosianModuloTwo he
    simp only [map_mul,icosianLocalDMatrix_reduction] at hm
    change (icosianNormOneReduction (g.val.left i) : IcosianMatrix)*icosianLocalDMatrix i=
      icosianLocalDMatrix i*(icosianNormOneReduction u : IcosianMatrix) at hm
    change icosianLocalDMatrix i*(icosianNormOneReduction u : IcosianMatrix)*
      icosianLocalDMatrixInverse i=_
    rw [← hm,mul_assoc,icosianLocalDMatrix_mul_inverse,mul_one]
  have hg := g.property
  change icosianMonomialReduction g.val∈icosianGlueMonomialStabilizer GoldenFour at hg
  rw [icosianGlueMonomialStabilizer_iff] at hg
  change IcosianGluePreserves (fun i => icosianNormOneReduction (g.val.left i)) at hg
  have hg' := icosianGlue_coefficients _ hg
  unfold IcosianLocalDReductionTest
  simp only [hc]
  exact hg'

end Atlas.Conway
