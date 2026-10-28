module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarFixedModule
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOutsideGuard
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixActionKernel
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete

/-!
# The actual whole secondary-module ratio bound

Apply proved source3.1.8 to V₀=U⟨Z_Y^K⟩ inside the unchanged KT.
Reducedness supplies the reverse core-centralizer inclusion; the faithful
original six-space U supplies the forward inclusion. The original failure
at C_G(z) constructs an outside HStar witness, so the numerical theorem
has its genuine standing guard rather than a retained callback.

Source: the q-hat upper bound in Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Bound the full original product module through its literal centralizer
quotient, with the outside-local guard constructed from the original hnot. -/
theorem original_tripleSix_central_closure_secondary_cubicRatio
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := K ⊔ (T : Subgroup G)
    let C := M.pCoreIn 2 ⊓ centralizer (tripleSixScalarResidual K : Set G)
    let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
    let V0 := (U ⊔ V).subgroupOf M
    ∃ hr : IsPReduced 2 V0,
      letI := hr.normal
      letI := hr.elementary
      cubicRatio (NormalElementaryQuotient.representation V0
        (QuotientGroup.mk' (centralizer (V0 : Set M)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let M := K ⊔ (T : Subgroup G)
  let C := M.pCoreIn 2 ⊓ centralizer (tripleSixScalarResidual K : Set G)
  let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
  let V0 := (U ⊔ V).subgroupOf M
  have hf := original_tripleSix_central_closure_scalar_fixed_module
    h structural D a z hz hzT hnot houter
  have hr : IsPReduced 2 V0 := hf.2.2.2.2.2.1
  have hUM : U ≤ M := D.le_component.trans le_sup_left
  have hcentral : (T : Subgroup G).subgroupOf M ⊓ centralizer (V0 : Set M)=pCore 2 M := by
    apply le_antisymm
    · intro x hx
      have hxu : (x:G) ∈ centralizer (U : Set G) := by
        intro u hu
        exact congrArg M.subtype (hx.2 ⟨u,hUM hu⟩ (show (⟨u,hUM hu⟩ : M) ∈ V0 from mem_sup_left hu))
      have hq : (x:G) ∈ M.pCoreIn 2 :=
        (original_tripleSix_action_kernel h structural D a).1 ⟨x.property,hxu⟩
      obtain ⟨k,hk,he⟩ := hq
      exact (show k=x from Subtype.ext he) ▸ hk
    · refine le_inf ?_ (le_centralizer_iff.mp hr.le_centralizer_pCore)
      exact pCore_isPGroup.le_sylow_of_normal (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right))
  obtain ⟨_,_,H,hH⟩ := original_tripleSix_central_closure_outside_guard
    h structural D z hz hzT hnot
  obtain ⟨hmax,huniq⟩ := h.source_normalizer_maximal_unique_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G:=X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G:=X))
  refine ⟨hr,?_⟩
  exact Chapter3.source_reduced_join_cubicRatio_le_two h.simpleQTKE T
    (normalizer (K : Set G)) K H h.maximal_faithful.2.1.2.1 K.le_normalizer
    (normal_subgroupOf_of_le_normalizer le_rfl) hmax
    (sup_le K.le_normalizer D.sylow_normalizes_component) huniq hH V0 hr hcentral

end CFSG.Quasithin.Chapter12.Section07
