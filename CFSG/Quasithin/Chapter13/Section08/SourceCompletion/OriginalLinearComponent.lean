module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalMiddleNode

/-!
# Binary linear components are excluded at the original ordinary A₆ source

The actual parabolic reduction and the constructed middle-node exclusion
force a triple-cover center of order three on the original L/O₂(L). Its
ordinary A₆ marking has trivial center, giving a contradiction. The source
component catalogue and all relative structure are constructed internally;
no uniform seven-point exclusion or universal local-input family is required.
Source: Aschbacher--Smith 13.8.21,25, printed pp.957,959--962.
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve
open Chapter2.ComponentRefinement.LieType.Binary

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- None of the binary linear rows survives on the actual original ordinary
source component. -/
theorem original_linear_component_false_of_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {n : ℕ} (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) : False := by
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer
    (localNaturalSetup d) eL hmax hm'
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  have components := FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
    d hmax hF9all hcentral hcomm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let eK : (K ⧸ pCore 2 K) ≃* PSL n := e.trans (Atlas.fieldEquivPSL n eF)
  obtain ⟨_,hc,_⟩ :=
    AlternatingAndLinear.LinearReduction.OriginalSource.binary_reduction_of_middle_exclusion
      d hmax hF9all hcentral hcomm (Components.EarlierResidual.original_source d hmax)
      components (fun _ _ hJ hCJ hC eJ =>
        original_middle_node_exclusion_of_plane_noncentral d eL hmax hF9all hm hJ hCJ hC eJ)
      hH hKH hK hn₀ hn₁ eK
  have hz := Nat.card_congr (centerCongr eL).toEquiv
  rw [hc.2.1,alternatingGroup.center_eq_bot (by simp),card_bot] at hz
  omega

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
