module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.Words
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.OddCenter

/-!
# Assembly boundary for the concrete F4 folding identification

The two literal root-word evaluations are surjective. Equality of their
kernels induces a multiplicative equivalence with exact compatibility on
both signed simple-root curves. The independently proved perfectness of
the F4 cover makes its central quotient centerless; an identification
therefore also supplies centerlessness of the folded subgroup.

The kernel equality is deliberately still an explicit premise: proving it
requires the actual comparison of the 52-dimensional F4 adjoint matrices
with the paired 78-dimensional E6 matrices. No identification or source
inclusion is claimed until both word-relation implications are discharged.
In particular, a Cartan-matrix equality does not supply this premise.

Source: the F4 inclusions used in Aschbacher--Smith A.2.17, printed p.39
of `refs/quasithin.pdf`; GLS3 §§2.2--2.6 for the concrete root groups and
central-quotient convention (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section

namespace TwistedE6.FoldedSubsystem.F4Identification
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq
local instance assemblyRootFintype : Fintype typeF4Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

private noncomputable def sameKernelEquiv {W G H : Type*} [Group W] [Group G] [Group H]
    (f : W →* G) (g : W →* H) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : G ≃* H :=
  (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))

private theorem sameKernelEquiv_apply {W G H : Type*} [Group W] [Group G] [Group H]
    (f : W →* G) (g : W →* H) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) (w : W) : sameKernelEquiv f g hf hg h (f w) = g w := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : e.symm (f w) = QuotientGroup.mk w := e.symm_apply_eq.mpr rfl
  change (QuotientGroup.quotientKerEquivOfSurjective g hg)
    ((QuotientGroup.quotientMulEquivOfEq h) (e.symm (f w))) = _
  rw [he, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- Conditional first-isomorphism assembly. The equality of word kernels remains to be proved. -/
noncomputable def equivOfEvaluationKernels
    (h : (sourceEvaluation F).ker = (foldedEvaluation F).ker) :
    ExceptionalSplit.F4 F ≃* splitSubgroup F :=
  sameKernelEquiv (sourceEvaluation F) (foldedEvaluation F)
    (sourceEvaluation_surjective F) (foldedEvaluation_surjective F) h

theorem equivOfEvaluationKernels_evaluation
    (h : (sourceEvaluation F).ker = (foldedEvaluation F).ker) (w : Word F) :
    equivOfEvaluationKernels F h (sourceEvaluation F w) = foldedEvaluation F w :=
  sameKernelEquiv_apply _ _ _ _ h w

@[simp] theorem equivOfEvaluationKernels_simple
    (h : (sourceEvaluation F).ker = (foldedEvaluation F).ker)
    (s : Bool) (i : Fin 4) (t : F) :
    equivOfEvaluationKernels F h (sourceSimple F s i t) = f4Simple F s i t := by
  simpa only [sourceEvaluation_of, foldedEvaluation_of] using
    equivOfEvaluationKernels_evaluation F h (FreeGroup.of (s, i, t))

theorem evaluationKernels_eq_of_relations
    (hforward : ∀ w : Word F,
      coverEvaluation F w ∈ Subgroup.center (Cover F) → foldedEvaluation F w = 1)
    (hbackward : ∀ w : Word F,
      foldedEvaluation F w = 1 → coverEvaluation F w ∈ Subgroup.center (Cover F)) :
    (sourceEvaluation F).ker = (foldedEvaluation F).ker := by
  ext w
  simp only [MonoidHom.mem_ker, sourceEvaluation_eq_one_iff]
  exact ⟨hforward w, hbackward w⟩

/-- Once the matrix identification is supplied, its target is centerless without another model theorem. -/
theorem splitSubgroup_center_of_equiv (htwo : (2 : F) ≠ 0)
    (e : ExceptionalSplit.F4 F ≃* splitSubgroup F) :
    Subgroup.center (splitSubgroup F) = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  have hs : e.symm z ∈ Subgroup.center (ExceptionalSplit.F4 F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    simpa using Subgroup.mem_center_iff.mp hz (e y)
  rw [source_center_eq_bot F htwo, Subgroup.mem_bot] at hs
  simpa using congrArg e hs

end TwistedE6.FoldedSubsystem.F4Identification
