module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbit.Structure
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelResidual.Commutators
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The residual action on the center and central quotient of the HS core

Conjugation is defined using the literal inclusion into `localGroup 0`.
Its restriction to the cyclic center kills the core and factors through the
published A₅ quotient. Perfection of A₅ and the abelian automorphism group of
a cyclic group make that action trivial. This uses no perfection or residual
identification theorem for the alternating preimage itself.

The core also acts trivially on its quotient by its center, since its
commutator subgroup is central. Factoring this second conjugation action
through `modelResidualQuotient` constructs the genuine A₅ action, with explicit
compatibility on quotient representatives. No A₅ action on the core is asserted.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

public section
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
open scoped commutatorElement
attribute [local instance] core_normal

noncomputable def modelCoreAction : modelResidual →* MulAut core :=
  (MulAut.conjNormal : localGroup 0 →* MulAut core).comp modelResidual.subtype

theorem modelCoreAction_apply (g : modelResidual) (x : core) :
    (modelCoreAction g x).val = g.val * x.val * g.val⁻¹ := by rfl

noncomputable def modelCoreCenterEquiv : center core ≃* C4 :=
  (MulEquiv.subgroupCongr model_core_center).trans
    (MonoidHom.ofInjective cyclicEmbedding_injective).symm

private noncomputable def centerAction : modelResidual →* MulAut (center core) :=
  (MulAut.characteristic (center core)).comp modelCoreAction

private theorem centerAction_kernel : core.subgroupOf modelResidual ≤ centerAction.ker := by
  intro g hg
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  change g.val * z.val.val * g.val⁻¹ = z.val.val
  have hc := congrArg Subtype.val (mem_center_iff.mp z.property (⟨g.val,hg⟩ : core))
  exact mul_inv_eq_iff_eq_mul.mpr hc

/-- The alternating preimage fixes the embedded center pointwise. -/
theorem modelResidual_fixes_center (g : modelResidual) (z : core)
    (hz : z ∈ center core) : g.val * z.val * g.val⁻¹ = z.val := by
  let : IsCyclic (center core) := isCyclic_of_surjective
    modelCoreCenterEquiv.symm.toMonoidHom modelCoreCenterEquiv.symm.surjective
  let : CommGroup (MulAut (center core)) :=
    (IsCyclic.mulAutMulEquiv (center core)).toMonoidHom.commGroupOfInjective
      (IsCyclic.mulAutMulEquiv (center core)).injective
  let f : modelResidual ⧸ core.subgroupOf modelResidual →* MulAut (center core) :=
    QuotientGroup.lift _ centerAction centerAction_kernel
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (modelResidual ⧸ core.subgroupOf modelResidual) :=
    Group.IsPerfect.ofSurjective (f := modelResidualQuotient.symm.toMonoidHom)
      modelResidualQuotient.symm.surjective
  have hf : f (QuotientGroup.mk' _ g) = 1 :=
    Abelianization.commutator_subset_ker f (Group.IsPerfect.mem_commutator)
  exact congrArg (fun a : MulAut (center core) => (a ⟨z,hz⟩).val.val) hf

/-- The source's central cyclic root is fixed by the actual residual action. -/
theorem modelResidual_fixes_cyclicGenerator (g : modelResidual) :
    g.val * cyclicGenerator.val * g.val⁻¹ = cyclicGenerator.val :=
  modelResidual_fixes_center g cyclicGenerator cyclicGenerator_mem_center

private noncomputable def coreQuotientAction : modelResidual →* MulAut (core ⧸ center core) :=
  (quotientAut (center core)).comp modelCoreAction

private theorem coreQuotientAction_kernel :
    core.subgroupOf modelResidual ≤ coreQuotientAction.ker := by
  intro g hg
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  induction v using Quotient.inductionOn with
  | h x =>
    let y : core := ⟨g.val,hg⟩
    have he : modelCoreAction g x = y * x * y⁻¹ := Subtype.ext rfl
    change quotientAut (center core) (modelCoreAction g) (QuotientGroup.mk' (center core) x) =
      QuotientGroup.mk' (center core) x
    rw [quotientAut_apply_mk]
    rw [he, map_mul, map_mul, map_inv]
    apply mul_inv_eq_iff_eq_mul.mpr
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply model_core_commutator_le_center
    exact commutator_mem_commutator (mem_top _) (mem_top _)

/-- The genuine induced A₅ action on the central quotient of the core. -/
noncomputable def modelA5CoreQuotientAction :
    alternatingGroup (Fin 5) →* MulAut (core ⧸ center core) :=
  (QuotientGroup.lift _ coreQuotientAction coreQuotientAction_kernel).comp
    modelResidualQuotient.symm.toMonoidHom

theorem modelA5CoreQuotientAction_compatible (g : modelResidual)
    (x : core) :
    modelA5CoreQuotientAction
        (modelResidualQuotient (QuotientGroup.mk' (core.subgroupOf modelResidual) g))
        (QuotientGroup.mk' (center core) x) =
      QuotientGroup.mk' (center core) (modelCoreAction g x) := by
  simp only [modelA5CoreQuotientAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  change quotientAut (center core) (modelCoreAction g) (QuotientGroup.mk' (center core) x) = _
  exact quotientAut_apply_mk (center core) (modelCoreAction g) x

theorem modelA5CoreQuotientAction_apply (g : modelResidual) (x : core) :
    modelA5CoreQuotientAction (modelResidualAction g) (QuotientGroup.mk' (center core) x) =
      QuotientGroup.mk' (center core) (modelCoreAction g x) :=
  modelA5CoreQuotientAction_compatible g x

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
