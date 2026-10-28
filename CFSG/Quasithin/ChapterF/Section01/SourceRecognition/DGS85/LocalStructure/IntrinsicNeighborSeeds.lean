module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicRadiusAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.NeighborCenters

/-!
# Natural neighbor seeds for the intrinsic critical actor

The original noncommuting critical action is natural and its central kernel
vanishes in a hypothetical long branch. The full edge Sylows identify each
neighbor center with the corresponding natural fixed space. The existing
complementary-fixed-space theorem now gives the literal direct product of
two distinct neighbor centers. Only the critical actor is recognized; no
marking on the other vertex orbit is assumed.

This supplies the actual seed decomposition used by the terminal
radius/core and centralizer arguments.
Source: DGS, *Groups and Graphs* (1985), (7.4) and (7.5)(1), pp.128--129.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- Distinct neighbors split the actual natural critical center. -/
theorem reduced_long_neighbor_centers_split (h : HypothesisF11 L S)
    {v w a t : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hva : (graph F).Adj v a) (hvt : (graph F).Adj v t) (hat : a ≠ t) :
    Z F v = Z F a ⊔ Z F t ∧ Disjoint (Z F a) (Z F t) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let := graph_Z_elementary ht v
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hcenter := reduced_long_critical_center_trivial h hc hne hb hva
  have hω : Stellmacher.omegaOneCenterAmbient M = ⊥ := by
    apply bot_unique
    intro z hz
    obtain ⟨hzM,_,hzC⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
    have hm : (⟨z,hzM⟩ : M) ∈ center M :=
      mem_center_iff.mpr (fun l => Subtype.ext (hzC l l.property))
    rw [hcenter,mem_bot] at hm
    exact congrArg Subtype.val hm
  have hnat : HasNaturalCenter M (Z F v) (Q F v) :=
    (reduced_critical_natural_centers_and_products h hc hne).1
  obtain ⟨k,hk,hfin,halg,π,hπ,_hk,⟨c⟩⟩ := hnat
  let c₀ : BinaryConjugationSection M (Z F v) ⊥
      (SL2NaturalOffenders.NoStrong.natural.comp π) := hω ▸ c
  have hsyl (x : Vertex F) (hx : (graph F).Adj v x) :
      ∃ R : Sylow 2 M, (R : Subgroup M).map M.subtype =
        (stabilizer F v ⊓ stabilizer F x).pCoreIn 2 := by
    obtain ⟨R,hR⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) hx
    obtain ⟨T,hT⟩ := R.exists_map_subtype_eq_of_le
      (H := M) (sylowGenerated_le _) (sylow_le_sylowGenerated _ R)
    exact ⟨T,hT.trans (sylow_image_eq_edge_core _ _ inf_le_left
      (source_edge_core_sylow ht (reduced_borel_core_sylow h) hx) R hR)⟩
  have heps (x : Vertex F) (hx : (graph F).Adj v x) :=
    (reduced_long_critical_neighbor_seed h hc hne hb hx).1
  have hseed (x : Vertex F) (hx : (graph F).Adj v x) : Z F x ≤ Z F v := by
    obtain ⟨d,hd⟩ := reduced_critical_actor_localData h hc hne hx
    change d.Pstar = M at hd
    rw [heps x hx]
    apply graph_edgeSeed_le_Z ht (reduced_borel_core_sylow h) hx d
    rw [hd]
    exact graph_actor_odd_index ht v
  have hf (x : Vertex F) (hx : (graph F).Adj v x)
      (R : Sylow 2 M) (hR : (R : Subgroup M).map M.subtype =
        (stabilizer F v ⊓ stabilizer F x).pCoreIn 2) :
      c₀.imageSpace (Z F x) = fixedSpace SL2NaturalOffenders.NoStrong.natural
        (R.mapSurjective (f := π) hπ) := by
    let E := (stabilizer F v ⊓ stabilizer F x).pCoreIn 2
    have hEM : E ≤ M := hR.symm.le.trans (map_subtype_le _)
    have hfixed : Z F v ⊓ centralizer (E : Set (G₀ L S)) = Z F x := by
      rw [heps x hx]
      apply elementary_fixed_eq_seed
      · exact ((source_Z_Q_U ht v).1.trans (map_subtype_le _)).trans (graph_Q_le_edgeCore ht hx)
      · exact (heps x hx).symm.le.trans (hseed x hx)
    have hpre : commutatorPreimage (Z F v) E ⊥ = Z F v ⊓ centralizer (E : Set (G₀ L S)) := by
      apply le_antisymm
      · exact le_inf (commutatorPreimage_le _ _ _)
          (commutator_eq_bot_iff_le_centralizer.mp
            (bot_unique (commutator_commutatorPreimage_le (Z F v) E ⊥ le_normalizer_of_normal)))
      · exact le_commutatorPreimage inf_le_left
          (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le
    have hER : E.subgroupOf M = R := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le hEM]
      exact hR.symm
    rw [←hfixed,←hpre,c₀.fixed_image_eq E hEM le_normalizer_of_normal,
      fixedSpace_comp_map,hER]
    rfl
  obtain ⟨R,hR⟩ := hsyl a hva
  obtain ⟨T,hT⟩ := hsyl t hvt
  let R' := R.mapSurjective (f := π) hπ
  let T' := T.mapSurjective (f := π) hπ
  have hRf := hf a hva R hR
  have hTf := hf t hvt T hT
  have hRT : R' ≠ T' := by
    intro he
    have himg : c₀.imageSpace (Z F a) = c₀.imageSpace (Z F t) :=
      hRf.trans ((congrArg (fun U : Sylow 2 SL(2,k) =>
        fixedSpace SL2NaturalOffenders.NoStrong.natural (U : Subgroup SL(2,k))) he).trans hTf.symm)
    apply graph_neighbor_centers_ne ht hva hvt hat
    apply le_antisymm
    · intro z hz
      apply (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed a hva hz⟩).mp
      rw [←himg]
      exact (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le _).mpr hz
    · intro z hz
      apply (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed t hvt hz⟩).mp
      rw [himg]
      exact (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le _).mpr hz
  have hcompl := natural_distinct_sylow_fixed_isCompl R' T' hRT
  refine ⟨c₀.section_eq_sup_of_imageSpace_sup_top _ _ (hseed a hva) (hseed t hvt) bot_le ?_,?_⟩
  · rw [hRf,hTf]
    exact hcompl.sup_eq_top
  · apply disjoint_iff.mpr
    apply bot_unique
    intro z hz
    have hza := (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed a hva hz.1⟩).mpr hz.1
    have hzt := (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed a hva hz.1⟩).mpr hz.2
    rw [hRf] at hza
    rw [hTf] at hzt
    have hz0 : (c₀.coordinates ⟨z,hseed a hva hz.1⟩).toAdd ∈ (⊥ : Submodule (ZMod 2) (Fin 2 → k)) := by
      rw [←hcompl.inf_eq_bot]
      exact ⟨hza,hzt⟩
    exact (c₀.coordinates_eq_one_iff _).mp hz0

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
