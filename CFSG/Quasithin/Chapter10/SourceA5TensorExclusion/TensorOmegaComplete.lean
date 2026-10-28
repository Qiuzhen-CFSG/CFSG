module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaChief
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalOvergroupModels
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalComplete

/-!
# The original tensor Omega core and its overgroup action

Apply the completed qrc bound to the actual larger module Ω₁Z(O₂(L₀T)).
Its faithful tensor submodule and the chief-section budget force the original
component to act trivially on the quotient. Cohomology and the proved
center-free source implication identify the whole Omega module with V.
The interval and stabilizer conclusions follow on the original subgroups.

The final consumer supplies this result to the field-four overgroup
classification. Its earlier marked E.2.7 premise is discharged; the actual
old-residual A₅ quotient, nonzero core, line centralization and plane movement
remain the independent source inputs of 9.3.

Source: Aschbacher--Smith 9.2.2 and 9.3.6--7, printed pp.730,733--734,
using the original qrc theorem 3.1.8(1).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The completed cubic bound acts on the entire central Omega module. -/
theorem omegaCenter_core_cubicRatio_le_two {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    cubicRatio (ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
      (omegaCenterIn ((localJoin T L).pCoreIn 2)) join_normalizes_omegaCenter_core) ≤ 2 := by
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  exact (m.omegaCenter_core_qrcHypotheses hH).source_cubicRatio_le_two
    D.simpleQTKE hu.1 hu.2.2 m.omegaCenter_core_ne_bot

/-- The actual component cannot move the larger Omega module beyond V. -/
theorem omegaCenter_core_commutator_le {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),localOrbit T L⁆ ≤ D.fullModule :=
  m.omegaCenter_core_commutator_le_of_cubicRatio_le_two
    (m.omegaCenter_core_cubicRatio_le_two hH)

/-- Source 9.2.2(1), with the original standing outside-local guard. -/
theorem fullModule_eq_omegaCenter_core
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    D.fullModule = omegaCenterIn ((localJoin T L).pCoreIn 2) := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  exact m.fullModule_eq_omegaCenter_core_of_outside_of_commutator_le hout
    (m.omegaCenter_core_commutator_le hH)

/-- Source 9.2.2(2) for every original intermediate two-subgroup. -/
theorem omegaCenter_eq_fullModule_inf
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (S : Subgroup G) (hQS : (localJoin T L).pCoreIn 2 ≤ S)
    (hST : S ≤ (T : Subgroup G)) :
    omegaCenterIn S = D.fullModule ⊓ centralizer (S : Set G) :=
  omegaCenter_eq_fullModule_inf_of_core_eq (m.fullModule_eq_omegaCenter_core hout) S hQS hST

/-- The original half-Sylow Omega center lies in the actual tensor line. -/
theorem omegaCenter_stabilizer_le_tensorLine_source
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    omegaCenterIn ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤ m.tensorLine := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  exact m.omegaCenter_stabilizer_le_tensorLine m.sylow_not_normalizes_component hout
    (m.omegaCenter_core_commutator_le hH)

/-- Original field-four action models with the Omega commutator, chosen cubic,
and stabilizer Sylow premises discharged by their proved source arguments. -/
theorem old_residual_overgroup_fourField_models_source
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      (pResidual 2 M₀).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData :=
  m.old_residual_overgroup_fourField_models_of_nonzero_core
    m.sylow_not_normalizes_component houtside
    (m.omegaCenter_core_commutator_le hH)
    hH eK M₀ hcore hgen hKU hmove


end CFSG.Quasithin.Chapter10.SourceA5TensorModel
