module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Frattini
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The actual module and Thompson family for the central branch

The earlier characteristic-two conclusion and Sylow-central seed put W_K
in Ω₁(Z(O₂(G_v))), hence in T_v. This constructs its normal elementary
realization inside K₋L_vT_v. Its centralizer is exactly the kernel of the
literal plus quotient. Injective transport identifies the internal
Thompson and Baumann subgroups with the original ambient subgroups.

The earlier equality K = [K,J(T_v)] forces J(T_v) to act nontrivially
on W_K, since K⁺ is nontrivial. Thus the nontriviality hypothesis in
B.2.20 is discharged without assuming a radical image.

`EarlierData` is a list of earlier source conclusions, not an assertion
that they follow here from Hypothesis 13.3.1. The central-branch assembly
must supply them from its full standing and marked A₅ hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.4, 13.6.6, the paragraph preceding 13.6.14, and 13.6.16(3),
printed pp.926–930; application in 13.6.20, printed p.931.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}

/-- Earlier source conclusions used by the B.2.20 application. In particular
the last equality is the genuine 13.6.16(3), not a Thompson image assertion. -/
structure EarlierData (K L T : Subgroup G) (z v : G) where
  selected : K ∈ Yz L T z v
  tvSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)
  normalizeL : Tv T v ≤ normalizer (Lv L v : Set G)
  fixSeed : Tv T v ≤ centralizer ({z} : Set G)
  normalizeK : Tv T v ≤ normalizer (K : Set G)
  seedOmega : z ∈ omegaOneCenterAmbient (Tv T v)
  characteristicTwo : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)
  baumann_eq : ChapterB.baumann T = ChapterB.baumann (Tv T v)
  component_generated : K = ⁅K, elementaryAbelianMaxJ (Tv T v)⁆

namespace EarlierData
variable (e : EarlierData K L T z v)
include e

theorem WK_le_coreOmega : WK K L T z v ≤ omegaOneCenterAmbient (Qv v) :=
  (WK_le_Uv K L T z v e.selected.1.1).trans
    (Uv_le_coreOmega T z v e.tvSylow e.seedOmega e.characteristicTwo)

theorem WK_le_Tv : WK K L T z v ≤ Tv T v := by
  obtain ⟨P, hP⟩ := e.tvSylow
  intro w hw
  exact (hP ▸ pCoreIn_le_sylow (Gv v) P)
    ((mem_omegaOneCenterAmbient_iff _ _).mp (e.WK_le_coreOmega hw)).1

theorem WK_le_actor : WK K L T z v ≤ plusActor K L T v :=
  e.WK_le_Tv.trans le_sup_right

/-- W_K in the actual plus actor. -/
def internalW (_e : EarlierData K L T z v) : Subgroup (plusActor K L T v) :=
  (WK K L T z v).subgroupOf (plusActor K L T v)

/-- The original T_v, restricted to the plus actor. -/
def internalR (_e : EarlierData K L T z v) : Subgroup (plusActor K L T v) :=
  (Tv T v).subgroupOf (plusActor K L T v)

instance internalW_normal : e.internalW.Normal :=
  normal_subgroupOf_of_le_normalizer
    (plusActor_normalizes_WK K L T z v e.normalizeL e.fixSeed)

instance internalW_elementary : IsElementaryAbelian 2 e.internalW := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv v)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (WK K L T z v) := IsElementaryAbelian.of_le e.WK_le_coreOmega
  exact IsElementaryAbelian.subgroupOf e.WK_le_actor

theorem internalW_le_internalR : e.internalW ≤ e.internalR :=
  comap_mono e.WK_le_Tv

/-- The quotient kernel is the full centralizer of the same internal W_K. -/
theorem plusMk_ker_internal :
    (plusMk K L T z v e.normalizeL e.fixSeed).ker =
      centralizer (e.internalW : Set (plusActor K L T v)) := by
  rw [plusMk_ker]
  ext a
  constructor
  · intro ha w hw
    exact Subtype.ext (ha w hw)
  · intro ha w hw
    exact congrArg Subtype.val (ha ⟨w, e.WK_le_actor hw⟩ hw)

/-- The faithful binary action used for the FF*-offender calculation. -/
noncomputable def plusRepresentation :=
  Representation.NormalElementaryQuotient.representation e.internalW
    (plusMk K L T z v e.normalizeL e.fixSeed)
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed) e.plusMk_ker_internal

theorem plusRepresentation_faithful : Function.Injective e.plusRepresentation :=
  Representation.NormalElementaryQuotient.representation_injective e.internalW
    (plusMk K L T z v e.normalizeL e.fixSeed)
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed) e.plusMk_ker_internal

omit [Finite G] in
theorem internal_thompson_map :
    (elementaryAbelianMaxJ e.internalR).map (plusActor K L T v).subtype =
      elementaryAbelianMaxJ (Tv T v) := by
  rw [← elementaryAbelianMaxJ_map_injective _ (plusActor K L T v).subtype_injective,
    internalR, map_subgroupOf_eq_of_le (show Tv T v ≤ plusActor K L T v from le_sup_right)]

omit [Finite G] in
theorem internal_baumann_map :
    (ChapterB.baumann e.internalR).map (plusActor K L T v).subtype =
      ChapterB.baumann T := by
  rw [ChapterB.baumann, ChapterB.thompsonAlpha, baumann_map_injective _
    (plusActor K L T v).subtype_injective, internalR,
    map_subgroupOf_eq_of_le (show Tv T v ≤ plusActor K L T v from le_sup_right),
    e.baumann_eq]
  rfl

omit [Finite G] e in
private theorem thompson_le_actor :
    elementaryAbelianMaxJ (Tv T v) ≤ plusActor K L T v :=
  (sSup_le fun _ hB => hB.1).trans le_sup_right

omit [Finite G] in
theorem internal_thompson_eq :
    elementaryAbelianMaxJ e.internalR =
      (elementaryAbelianMaxJ (Tv T v)).subgroupOf (plusActor K L T v) := by
  apply map_injective (plusActor K L T v).subtype_injective
  rw [e.internal_thompson_map, map_subgroupOf_eq_of_le thompson_le_actor]

omit [Finite G] in
theorem internal_baumann_eq :
    ChapterB.baumann e.internalR =
      (ChapterB.baumann T).subgroupOf (plusActor K L T v) := by
  apply map_injective (plusActor K L T v).subtype_injective
  rw [e.internal_baumann_map, map_subgroupOf_eq_of_le (show ChapterB.baumann T ≤
    plusActor K L T v by rw [e.baumann_eq]; exact inf_le_left.trans le_sup_right)]

omit [Finite G] in
/-- The source commutator generation excludes a trivial Thompson image. -/
theorem thompson_not_le_kernel :
    ¬ elementaryAbelianMaxJ e.internalR ≤
      (plusMk K L T z v e.normalizeL e.fixSeed).ker := by
  intro hJ
  let H := plusActor K L T v
  let J := elementaryAbelianMaxJ (Tv T v)
  have hJH : J ≤ H := thompson_le_actor
  have hKH : K ≤ H := K_le_plusActor K L T v
  have hc : (⁅K, J⁆).subgroupOf H = ⁅K.subgroupOf H, J.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup K J).trans (sup_le hKH hJH)),
      map_commutator, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hJH]
  have hgen : K.subgroupOf H = ⁅K.subgroupOf H, J.subgroupOf H⁆ := by
    rw [← hc, ← e.component_generated]
  have hbot : (J.subgroupOf H).map
      (plusMk K L T z v e.normalizeL e.fixSeed) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (e.internal_thompson_eq ▸ hJ)
  apply plusImage_ne_bot_of_mem_Yz K L T z v e.normalizeL e.fixSeed e.selected
  change (K.subgroupOf H).map (plusMk K L T z v e.normalizeL e.fixSeed) = ⊥
  rw [hgen, map_commutator, hbot, commutator_bot_right]

end EarlierData
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
