module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixPlusComponent
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryPlusKernelFaithful
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryFixedLayerCentrality

/-!
# Excluding the ordinary nonabelian full-span branch

For the maximal natural-six counterexample, the original plus action is
faithful modulo the two-core. Its full-span construction selects a genuine
component and offender. The completed fixed-layer theorem then supplies
centralization for that same component, so the selected-component
contradiction applies without any component-selection, kernel-equality or
fixed-layer premise.

The earlier plane noncentrality, Baumann bound and genuine 13.3.2 component
and module classifications remain explicit inputs of their source owners.
Source: Aschbacher–Smith 13.7.4, 13.7.15–21, printed pp.937–946.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion Chapter13.Section07 ChapterF.Section09.Setup
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The maximal ordinary counterexample cannot have a nonabelian full span
once its genuine earlier source inputs are supplied. -/
theorem original_six_nonabelian_false_of_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hBnormal : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    False := by
  have hk := original_six_plus_kernel_eq_of_source d hmax eL hV hm hBnormal h1332 modules
  obtain ⟨g,hsquare,hspan,hout,hE,σ,s,B,K,hf,hB,hBA,hBC,hKC,hKs,hBK,hcomm,
    hdim,hmove,hIrr,ha,hKn,hwhole⟩ :=
    original_six_full_span_component d hmax eL hV hm hk
  let := hE
  have hKM : (K.map G₁.subtype).subgroupOf G₁ = K :=
    comap_map_eq_self_of_injective G₁.subtype_injective K
  have hstar : Chapter13.Section08.Source.starImage G₁ (K.map G₁.subtype) =
      K.map (QuotientGroup.mk' (pCore 2 G₁)) := by
    change ((K.map G₁.subtype).subgroupOf G₁).map _ = _
    rw [hKM]
  apply original_six_selected_false_of_source1332 d hmax eL hV hm
    (inclusion le_sup_left g) hsquare hout σ s B hB hBA (map_subtype_le K)
  · rwa [hKM]
  · rwa [hstar]
  · exact hk
  · rwa [hstar]
  · exact hspan
  · exact hBnormal
  · exact h1332

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
