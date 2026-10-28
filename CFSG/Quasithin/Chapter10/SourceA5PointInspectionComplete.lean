module
public import CFSG.Quasithin.Chapter10.SourceA5PointAllSelection
public import CFSG.Quasithin.Chapter10.SourceA5PointInspectionAssembly

/-!
# Complete inspection of the original A₅ point components

Covering uniqueness stabilizes the original component at every escaping
point. The complete quasisimple carrier inspection and constrained action
inspection therefore cover the literal point component without an embedding
or marking callback. The chosen minimal-setup consumer derives its module
irreducibility from the proper-seed theorem after excluding the tensor case.
Only the independent local cubic bound and tensor exclusion remain there.

Source: Aschbacher–Smith 10.2.9–12, printed pp.750–754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance inspectionCompleteMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The actual enlarged quasisimple component has a proved source marking;
this includes points fixed by the original full local orbit. -/
theorem source_a5_point_quasisimple_marking_input
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G))) :
    SourceA5PointQuasisimpleMarkingInput.{u,0} D v := by
  intro I hLI hIX hI _ hout _ hquasi
  let := hquasi
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
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
  have hstab := source_a5_escaping_element_sylow_stabilizes D e hn
    (D.fullModule_le_sylow hu hvV) hvne (hcross hv) (fun hc => hout (hIX.trans hc))
  exact source_a5_point_quasisimple_marking_of_normalizes
    D e hi t hv hvne hstab hs hLI hIX hI

/-- Both component branches of the original point inspection are now proved. -/
theorem source_a5_point_component_inspection
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t v : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G))) :
    SourceA5PointComponentInspection D e t v :=
  source_a5_point_inspection_of_quasisimple_markings D e hi ht htn hcross hv hvne hs
    (source_a5_point_quasisimple_marking_input D e hi ht htn hcross hv hvne hs)

/-- The chosen original irreducible moved section now gives all point
centralizer containments and the weak-closure lower bound. -/
theorem source_a5_point_control_of_irreducible
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hcent := source_a5_moved_point_centralizers_of_irreducible_inspection D e hi
    (source_a5_baumann_normalizer_le D e hn) ht htn hcross
    (fun _ hv hvne hs => source_a5_point_component_inspection D e hi ht htn hcross hv hvne hs)
  exact ⟨hcent,source_a5_globalW_gt_one D e hi hn ht htn hcross hcent⟩

/-- Original point control and weak closure with every component-inspection
premise discharged; the local cubic and tensor branches remain independent. -/
theorem source_a5_point_control_after_tensor_exclusion
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hlocal : SourceLocalModuleCubicBound D)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ¬ Nonempty (SourceA5TensorModel D e)) :
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) := by
  have hproper := source_a5_seed_ne_local_of_no_tensor D e hn hD hmany hnot
  obtain ⟨_,hi,hcross,_⟩ :=
    source_a5_original_proper_seed_control D e hn ht htn hD hproper hlocal hmany
  exact source_a5_point_control_of_irreducible D e hi ht htn hcross

end CFSG.Quasithin.Chapter10
