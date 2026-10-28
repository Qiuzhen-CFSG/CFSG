module
public import CFSG.Quasithin.Chapter10.SourceA5PointA7Models
public import CFSG.Quasithin.Chapter10.SourceA5PointA7Four
public import CFSG.Quasithin.Chapter10.SourceA5PointA7Deleted
public import CFSG.Quasithin.Chapter10.SourceA5PointDeletedActor
public import CFSG.Quasithin.Chapter10.SourceA5PointDeletedFive

/-!
# The constrained point-component inspection

The actual Thompson action leaves only the two alternating-seven models.
The four-dimensional model identifies the original orbit with the original
moved factor. The deleted-seven model reconstructs the original head through
C.1.24 and restricts its original module to the prescribed deleted A5 module.
These give the literal exceptional and ordinary alternatives in 10.2.9.
Source: Aschbacher–Smith 10.2.9, printed pp.751–753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The original constrained component satisfies a source inspection alternative,
with all action, quotient, fixed-space and model premises discharged. -/
theorem source_a5_point_constrained_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hnot : ¬ IsQuasisimple I) (hout : ¬ I ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G))) :
    SourceA5PointComponentAlternative D e t I := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hNW := source_a5_moved_normalizer_le D e ht htn hcross
  have hCW := (Subgroup.centralizer_le_normalizer _).trans hNW
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hmapV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  have hvV : v ∈ D.fullModule := hmapV ▸ map_mono hWV hv
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  have hvT := D.fullModule_le_sylow hu hvV
  have hspan := source_a5_escaping_point_component_fixed_span_contains D e hi hn hvT hvne
    (hcross hv) (fun hc => hout (hIX.trans hc)) I hLI
  obtain ⟨hr,hAN,hfull,h,hmodel⟩ := source_a5_point_a7_models_of_partner D e hi
    ht htn hcross hv hvne I hLI hIX hI hNI hnot hout hs
  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
  let := hr.normal
  let := hr.elementary
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  let C := A.subgroupOf N
  have hfullC : moved ((action U).comp N.subtype) C = ⊤ := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact hfull
  cases hmodel with
  | four hirre eC hd =>
    have hdU := (SourceA5PointFFModels.alternatingSevenFour_original_model
      ((action U).comp N.subtype) C h.sectionData hfullC hirre eC hd).2.2
    exact source_a5_point_four_alternative D e I hLI hspan hr hdU
  | deleted hirre m =>
    obtain ⟨hc,a,_⟩ := SourceA5PointFFModels.alternatingSevenDeleted_original_model
      ((action U).comp N.subtype) C h.sectionData hfullC hirre m
    let E : A ≃* C := (subgroupOfEquivOfLe hAN).symm
    let eA : A ≃* alternatingGroup (Fin 7) := E.trans a.groupEquiv
    obtain ⟨c⟩ := source_a5_point_deleted_five D e I hLI hIX hI hNI hout hCW hs
      hspan hr eA a.linearEquiv (fun x w => a.intertwines (E x) w)
    obtain ⟨q,hq,hk,hIq,F,hF⟩ := source_a5_point_deleted_actor D I hNI hr hAN
      h.sectionData hfullC hc m
    have hJP := source_a5_partner_thompson_eq_of_irreducible D e hi ht hv
      (hs.restrict (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right)
        inf_le_right)
    obtain ⟨eI⟩ := source_a5_point_deleted_quotient D hvV hvne (hcross hv) I hLI hIX
      hI hNI hnot hout hCW hs hJP hspan hr q hq hk hIq F hF
    exact .ordinary c eI

end CFSG.Quasithin.Chapter10
