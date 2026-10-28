module
public import CFSG.Quasithin.Chapter10.SourceA5PointActionModels
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalImage
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedKernel.FixedSpan

/-!
# All-point model data for the constrained component

The escaping point centralizer supplies the fixed-span hypothesis, including
points in the central fixed kernel. The actual reduced orbit action then
satisfies the complete B.5.1 conclusion, is fully moved by the component,
and retains the proper local A5 section at the image of the original Sylow
subgroup. Source: Aschbacher–Smith 10.2.9, printed pp.750–753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The literal all-point action has its complete source model and the
proper marked local section needed by the model sieve. -/
theorem source_a5_point_constrained_model_data
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hv : v ∈ D.fullModule) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hnot : ¬ IsQuasisimple I) (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hJP : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G)) :
    let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ S
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
    ∃ hr : IsPReduced 2 U, letI := hr.normal; letI := hr.elementary
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action U).comp (offenderSubgroup (action U)).subtype)
        (((I.subgroupOf H).map (actionMk U)).subgroupOf (offenderSubgroup (action U)))) ∧
      ChapterB.QuasisimpleSource.moved (action U) ((I.subgroupOf H).map (actionMk U)) = ⊤ ∧
      let q := actionMk U
      let K := I.subgroupOf H
      let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
      B < ⊤ ∧ Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) ∧
        ∃ R : Sylow 2 K,
          (R : Subgroup K) = ((T : Subgroup G).subgroupOf H).subgroupOf K ∧
          B ∈ ChapterA.Section03.localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  have hvT := D.fullModule_le_sylow hu hv
  have hescape : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal :=
    fun hc => hout (hIX.trans hc)
  have hspan := source_a5_escaping_point_component_fixed_span_contains D e hi hn hvT hvne hvL hescape I hLI
  obtain ⟨hr,hmodel⟩ := source_a5_point_quasisimple_source_conclusion D hn ht hcross hv hvne hvL
    I hLI hIX hI hNI hnot hout hCW hs hJP hspan
  refine ⟨hr,hmodel,source_a5_point_action_fully_moved D I hLI hout hCW hspan hr,?_⟩
  exact source_a5_point_small_image_local_data D e I hLI hIX hI hNI hout hCW hs hspan hr
end CFSG.Quasithin.Chapter10
