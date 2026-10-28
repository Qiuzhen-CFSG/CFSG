module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LocalActorAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.RankOnePaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking
public import Theory.GroupTheory.AmalgamGraph.LinearPathKernel

/-!
# Constructing the actual local actor data for Chapter 7

The intrinsic Sylow span has odd index and the same embedded two-core as
its finite vertex stabilizer. The full edge normalizer identity supplies
its literal Sylow normalizer, so a rank-one model of this actor quotient
constructs all fields of `LocalRankOneData` on every edge. The canonical
source application also discharges the full-catalogue branching premise.

Only recognition of the enlarged actor quotients and the earlier (6.5)
obstruction remain in the general distance theorem. These are genuine
Chapter 6 inputs, not conclusions contained in a local-data record.
Source: DGS, Groups and Graphs (1985), (6.1)--(6.2), pp.118--119,
(6.5)--(6.7), pp.121--123, and (7.1)--(7.5), pp.126--131.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Every vertex Sylow lies in the intrinsic actor, making its index odd. -/
theorem graph_actor_odd_index (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    ¬ 2 ∣ (graphLocalGroup (family P) v).relIndex (stabilizer (family P) v) := by
  let := finite_endpoints h
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := stabilizer (family P) v)
  have hle : (T : Subgroup (stabilizer (family P) v)) ≤
      (graphLocalGroup (family P) v).subgroupOf (stabilizer (family P) v) := by
    intro t ht
    exact sylow_le_sylowGenerated _ T (mem_map_of_mem _ ht)
  exact fun hd => T.not_dvd_index (hd.trans (index_dvd_of_le hle))

/-- Construct the exact edge-local data from the actual actor quotient model. -/
theorem graph_actor_localData_exists (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w)
    (hm : IsRankOneModel (graphLocalGroup (family P) v ⧸
      pCore 2 (graphLocalGroup (family P) v))) :
    ∃ d : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) w),
      d.Pstar = graphLocalGroup (family P) v := by
  let := finite_endpoints h
  let L := graphLocalGroup (family P) v
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS he
  have hTe := Theory.GroupTheory.AmalgamGraph.sylow_image_eq_edge_core
    (stabilizer (family P) v) E inf_le_left (source_edge_core_sylow h hB he) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H := L)
    (sylowGenerated_le _) (sylow_le_sylowGenerated _ T)
  have hRe : (R : Subgroup L).map L.subtype = E.pCoreIn 2 := hR.trans hTe
  refine ⟨{
    finite_P := inferInstance
    Pstar := L
    Pstar_le := sylowGenerated_le _
    normal := normal_subgroupOf_of_le_normalizer (sylowGenerated_normalized _)
    same_core := sylowGenerated_core _
    supplement := graphLocalGroup_sup_edge h hB hS he
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (source_vertex_core_selfCentralizing h v)
    sylow := R
    borel_eq := ?_
    quotient := hm },rfl⟩
  rw [hRe]
  have hn := source_edge_core_normalizer h hB he
  apply le_antisymm
  · exact le_inf inf_le_left ((inf_le_right : L ⊓ E ≤ E).trans
      (E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))))
  · exact le_inf inf_le_left (fun x hx => hn ▸
      (show x ∈ stabilizer (family P) v ⊓ normalizer (E.pCoreIn 2 : Set G) from
        ⟨sylowGenerated_le _ hx.1,hx.2⟩))

/-- Every edge uses the intrinsic actor, once its actual quotient model is supplied. -/
def graphActorLocalData (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hm : ∀ v : Vertex (family P), IsRankOneModel (graphLocalGroup (family P) v ⧸
      pCore 2 (graphLocalGroup (family P) v)))
    (v w : Vertex (family P)) (he : (graph (family P)).Adj v w) :
    LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) w) :=
  (graph_actor_localData_exists h hB hS he (hm v)).choose

/-- The constructed starred actor is the original intrinsic graph actor. -/
theorem graphActorLocalData_star (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hm : ∀ v : Vertex (family P), IsRankOneModel (graphLocalGroup (family P) v ⧸
      pCore 2 (graphLocalGroup (family P) v)))
    (v w : Vertex (family P)) (he : (graph (family P)).Adj v w) :
    (graphActorLocalData h hB hS hm v w he).Pstar = graphLocalGroup (family P) v :=
  (graph_actor_localData_exists h hB hS he (hm v)).choose_spec

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Both Chapter 7 branches with all local data, odd indices and branching constructed. -/
theorem reduced_distance_bound_of_actor_models (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤
      normalizer ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    HasNaturalCenter (graphLocalGroup F v) (Z F v) (Q F v) ∧
    HasNaturalCenter (graphLocalGroup F w) (Z F w) (Q F w) := by
  let ht := reduced_triple h
  exact reduced_noncommuting_distance_bound_of_odd_localData h (graphLocalGroup F)
    (graphActorLocalData ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm)
    (graphActorLocalData_star ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm)
    (graph_actor_odd_index ht) hob hc hne (reduced_rankOne_branching h)

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

