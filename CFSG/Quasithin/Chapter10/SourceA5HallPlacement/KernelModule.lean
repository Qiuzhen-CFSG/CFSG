module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalSeparatedCentralizer
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
/-!
# The orbit section kernel fixes the original module

The two-core of L₀ centralizes the full reduced module. Therefore the
section centralizer of L₀ maps into the orbit centralizer in the faithful
full actor. When the separated original coordinates kill that latter
centralizer, the whole section kernel fixes V. This supplies exactly
Hypothesis4.4.1(3) for the original Hall kernel, without a non-FF split.

Source: Aschbacher–Smith10.2.3, printed p.745, using10.1.3 and D.3.21.
The separated-coordinate theorem remains the independent earlier input.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual faithful-actor centralizer calculation makes the source
section kernel centralize the full original module. -/
theorem source_orbit_sectionKernel_centralizes_fullModule
    (hc : let U := D.fullModule.subgroupOf D.maximalLocal
      let := (source_full_module_reduced D).normal
      let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
      let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
      centralizer (J : Set (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))) = ⊥) :
    sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G) := by
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let X := (localOrbit T L).subgroupOf M
  let C := (sectionCentralizer (localOrbit T L)).subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let J := X.map q
  have hCM : sectionCentralizer (localOrbit T L) ≤ M :=
    ((le_sectionCentralizer_iff (sectionCentralizer (localOrbit T L)) _).mp le_rfl).1
  have hXM : localOrbit T L ≤ M := (localOrbit T L).le_normalizer
  have hCX : ⁅C,X⁆ ≤ pCore 2 M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hCM,map_subgroupOf_eq_of_le hXM]
    exact (((le_sectionCentralizer_iff (sectionCentralizer (localOrbit T L)) _).mp le_rfl).2).trans
      (pCoreIn_mono_of_normalizes hXM le_rfl)
  have hCore : pCore 2 M ≤ centralizer (U : Set M) :=
    le_centralizer_iff.mp ((source_full_module_reduced D).le_reducedPSubgroup.trans
      (reducedPSubgroup_le_centralizer_pCore 2 M))
  have hcomm : ⁅C.map q,J⁆ = ⊥ := by
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact hCX.trans hCore
  have hCb : C.map q = ⊥ := bot_unique
    ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans_eq hc)
  have hC : C ≤ centralizer (U : Set M) := by
    have hh := (Subgroup.map_eq_bot_iff _).mp hCb
    simpa only [q,QuotientGroup.ker_mk'] using hh
  intro c hc v hv
  let vM : M := ⟨v,(D.fullModule_le_orbit.trans hXM) hv⟩
  exact congrArg Subtype.val
    (hC (show (⟨c,hCM hc⟩ : M) ∈ C from hc) vM (show vM ∈ U from hv))
/-- Bounded separated coordinates of the original full module discharge the
kernel-on-module premise in the Hall-placement argument. -/
theorem source_a5_hall_sectionKernel_centralizes_of_bounded_coordinates
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn) :
    sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G) := by
  obtain ⟨τ,i,hτ,hi,_,hc⟩ := hcoords
  exact source_orbit_sectionKernel_centralizes_fullModule D
    (source_a5_original_actor_centralizer_eq_bot_of_bounded_coordinates
      D e hn ht htn τ i hτ hi hc)
end CFSG.Quasithin.Chapter10
