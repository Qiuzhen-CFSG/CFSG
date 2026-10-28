module
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedKernel.Stabilization
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Completion
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion

/-!
# Point-centralizer completion with a positive fixed kernel

Covering uniqueness supplies the component stabilizer for every escaping
partner point, including points fixed by L₀. The existing five inspection
alternatives therefore apply without a separate fixed-point centralizer
hypothesis. Local Sylow saturation and conjugation give centralizer control
for all original moved vectors.

The only independent inputs are Sylow promotion and component inspection
for all nonidentity partner points. The source module and inspection owners
supply those inputs for the chosen setup; no assertion about arbitrary
module markings is made here. Source: Aschbacher–Smith 10.2.9, pp.750–753,
using the covering-uniqueness replacement for its initial reduction.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The existing inspection now controls every nonzero partner vector,
without requiring that it move under L₀. -/
theorem source_a5_partner_point_centralizer_le_of_all_point_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hinspect : SourceA5PointComponentInspection D e t v) :
    centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hmapV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  have hvV : v ∈ D.fullModule := hmapV ▸ (map_mono hWV hv)
  have hCW := (Subgroup.centralizer_le_normalizer _).trans hNW
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  by_contra hout
  obtain ⟨I,hLI,hIX,hI,hNI,hIM,hgen⟩ := source_a5_escaping_element_component_all_points D e hNL hn
    (D.fullModule_le_sylow hu hvV) hvne (hcross hv) hs hout
  apply source_a5_point_component_alternatives_impossible D e hn ht htn hsep hNL hNW
    hv hvne I hLI.le hIX hI hNI hIM
  apply hinspect I hLI hIX hI hNI hIM hgen
  by_cases hq : IsQuasisimple I
  · exact .inl hq
  · exact .inr ⟨source_a5_point_component_characteristicTwo D hvV hvne (hcross hv) hCW I hIX hI hq,
      source_a5_point_component_reduced_module D hvV hvne (hcross hv) hCW I hLI.le hIX hI hNI hq hs⟩

/-- The all-point endpoint with both original normalizer bounds discharged. -/
theorem source_a5_partner_point_centralizer_le_of_cross_all_point_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hinspect : SourceA5PointComponentInspection D e t v) :
    centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hsep : L.map (MulAut.conj t).toMonoidHom ≤ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D ht htn hcross))
  exact source_a5_partner_point_centralizer_le_of_all_point_inspection D e hn ht htn hsep hcross
    (source_a5_component_normalizer_le D e hn)
    (source_a5_moved_normalizer_le D e ht htn hcross) hv hvne hs hinspect

/-- Literal 10.2.9 completion with no separate fixed-kernel premise.
Sylow promotion and inspection cover all nonidentity partner points. -/
theorem source_a5_moved_point_centralizers_of_all_point_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hpromote : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  apply source_a5_moved_point_control_of_partner_saturated D hn ht htn
  intro v hv hvne hsM
  have hs := hpromote v hv hvne hsM
  exact source_a5_partner_point_centralizer_le_of_cross_all_point_inspection D e ht htn
    hcross hv hvne hs (hinspect v hv hvne hs)

end CFSG.Quasithin.Chapter10
