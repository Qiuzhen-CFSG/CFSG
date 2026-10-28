module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceCommutingThree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SmallAlphaExclusions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedCenterOrder

/-!
# The original mixed commuting-one numerical branch

The binary linear endpoint cannot be the directed critical alpha in the
commuting distance-one case. Thus every such critical edge is oriented
from the A₅ type to the S₃ type. Translating that directed edge to the
literal base edge allows the existing Chapter 11 source count to apply:
the full Borel two-core has order 64 and the original Sylow has order
64 or 128. Criticality is transported, never reversed.

Source: DGS, *Groups and Graphs* (1985), (11.4)--(11.7), pp.171--175,
and (15.1), p.226; Aschbacher--Smith F.1.12(I), pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open CFSG.Quasithin.ChapterF.Source.DGS85
open CommutingNontrivial CommutingOneProfile
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

/-- The critical orientation is determined by the original mixed markings. -/
theorem commuting_one_orientation (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta : Vertex F} (hc : IsCriticalPair F a beta)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F beta⁆ = ⊥) :
    a.type = false ∧ beta.type = true := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  have hab := source_critical_one_adjacent hc hb
  have hat : a.type = false := by
    by_contra hnot
    have hat : a.type = true := by cases he : a.type <;> simp_all
    have hval := mixed_reduced_neighbor_cards K U S h eK eU beta
    have hn : 1 < ((graph F).neighborSet beta).ncard := by
      rw [←Nat.card_coe_set_eq,hval]
      cases beta.type <;> decide
    obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard hn a
    exact source_alpha_linear_field_card_ne_two ht (Reduction.reduced_borel_core_sylow h)
      d hc hb hcomm hbc hca.symm (graph_models h eK eU beta)
      (graph_linear_two h eU a hat).some (by norm_num [Nat.card_eq_fintype_card])
  refine ⟨hat,?_⟩
  cases hbt : beta.type
  · exact False.elim (hab.1 (hat.trans hbt.symm))
  · rfl

/-- The actual directed base edge is critical, with commuting centers. -/
theorem commuting_one_base_critical (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta : Vertex F} (hc : IsCriticalPair F a beta)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F beta⁆ = ⊥) :
    IsCriticalPair F (base F false) (base F true) ∧
      ⁅Z F (base F false),Z F (base F true)⁆ = ⊥ := by
  obtain ⟨hat,hbt⟩ := commuting_one_orientation h eK eU hc hb hcomm
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hga,hgb⟩ := incident_common_translate F hab.2
  rw [hat] at hga
  rw [hbt] at hgb
  have hc' := CommutingNontrivial.criticalPair_translate F hc g⁻¹
  have hm := commuting_centers_translate F a beta g⁻¹
  rw [hcomm,Subgroup.map_bot] at hm
  rw [←hga,←hgb,inv_smul_smul,inv_smul_smul] at hc' hm
  exact ⟨hc',hm⟩

/-- The existing exact core count applies to any original commuting critical edge. -/
theorem commuting_one_size (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta : Vertex F} (hc : IsCriticalPair F a beta)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F beta⁆ = ⊥) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  obtain ⟨hc',hcomm'⟩ := commuting_one_base_critical h eK eU hc hb hcomm
  exact mixed_binary_graph_exact_row_size K U S h eK eU hc' hb hcomm'

/-- Every commuting critical pair has the exact small orders. The source
distance and predecessor are constructed internally from the original graph. -/
theorem commuting_size (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a a' : Vertex F} (hc : IsCriticalPair F a a')
    (hcomm : ⁅Z F a,Z F a'⁆ = ⊥) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  have ht := Reduction.reduced_triple h
  have hne : a' ≠ a := by
    intro he
    have hp : 0 < DGS85.b F := source_b_positive ht
    have hd := hc.1
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨beta,hab,hd⟩ := exists_predecessor F ht.generate a' a hne
  rw [SimpleGraph.dist_comm (u := a') (v := beta),
    SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hd
  exact commuting_one_size h eK eU hc
    (commuting_distance_one h eK eU hc hab hd hcomm) hcomm

end CFSG.Quasithin.ChapterF.Source.MixedDGS
