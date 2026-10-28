module
public import CFSG.Quasithin.Chapter10.SourceA5PairedBaumann
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerModule

/-!
# The exact Baumann action kernel in the zero-centralizer branch

The original local module equals the elementary abelian two-core of L₀T.
Characteristic two therefore identifies its centralizer with the module
itself. The paired Baumann marking consequently describes the quotient by
the actual local core, rather than a further centralizer quotient.

This is the action-and-kernel input to the four-dihedral-factor calculation
in Aschbacher–Smith 10.2.1, printed pp.742–743. Constructing the corresponding
involution lifts remains a separate group-extension step.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- In the original zero-centralizer branch, the local module is exactly
its own centralizer inside L₀T. -/
theorem source_a5_zero_centralizer_local_module_centralizer
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) =
      D.moduleSubgroup.subgroupOf (localJoin T L) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  have hu : U = pCore 2 H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 H))]
    exact source_a5_zero_centralizer_module_eq_core D e hn hout hz
  have hH : H ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, show (T : Subgroup G) ≤ H from le_sup_right⟩
    exact fun he => D.module_ne_bot (bot_unique (D.module_le_core.trans_eq he))
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (D.simpleQTKE.evenCharacteristic T) hH)
  have hU : IsElementaryAbelian 2 U := (source_parabolic_module_reduced D).elementary
  let := hU
  change centralizer (U : Set H) = U
  exact le_antisymm (by simpa only [hu] using hc) U.le_centralizer

/-- The original paired action has precisely the local two-core as kernel. -/
theorem source_a5_zero_centralizer_paired_action
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    SourcePairedBaumannAction D ∧
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) =
        pCore 2 (localJoin T L) := by
  refine ⟨source_a5_paired_baumann_action D e hn hout,?_⟩
  rw [source_a5_zero_centralizer_local_module_centralizer D e hn hout hz]
  apply Subgroup.map_injective (localJoin T L).subtype_injective
  rw [map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 (localJoin T L)))]
  exact source_a5_zero_centralizer_module_eq_core D e hn hout hz

end CFSG.Quasithin.Chapter10
