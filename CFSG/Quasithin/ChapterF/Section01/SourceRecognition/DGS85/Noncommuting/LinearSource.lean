module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ActorData
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearGraphApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearValence

/-!
# The noncommuting distance theorem for two original linear quotients

The two original PSL₂ markings construct the actual enlarged graph actors.
Their quotient models supply the local data, and the proved linear (6.5)
obstruction applies in the reversed orientation required by Chapter 7.
Thus both epsilon branches give b = 1 or b = 2, with actual natural centers.
The Sylow omega-center parameter also identifies the two actual defining
field orders in the original markings.
No local-data, odd-index, branching or obstruction callbacks remain.

Both original markings are required. Recognition of two critical endpoints
in the same vertex orbit does not provide the other orbit's marking.
The full nonlinear source theorem remains a separate assembly obligation.
Source: DGS, Groups and Graphs (1985), (6.1), pp.118--119,
(6.5), pp.121--122, and (7.1)--(7.5), pp.126--131.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Transport both base markings to the actual intrinsic actor at every vertex. -/
theorem graph_actor_models_of_linear (h : LocallyRankOneTriple P B)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (graphLocalGroup (family P) (base (family P) i) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) i))) ≃* SL(2,K i))
    (v : Vertex (family P)) :
    IsRankOneModel (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) := by
  let : Fintype (K v.type) := Fintype.ofFinite _
  obtain ⟨n,_,hcard⟩ := FiniteField.card (K v.type) 2
  let eSL : SL(2,K v.type) ≃* PSL(2,K v.type) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K v.type))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact .linear n n.pos ⟨K v.type,inferInstance,inferInstance,
    (Nat.card_eq_fintype_card).trans hcard,⟨(source_linear_quotient_at h K e v).trans eSL⟩⟩

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The linear source branch discharges every premise of the Chapter 7 distance argument. -/
theorem reduced_linear_noncommuting_distance_bound (h : HypothesisF11 L₀ S₀)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L₀ i ⧸ pCore 2 (family L₀ i)) ≃* PSL(2,K i))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    HasNaturalCenter (graphLocalGroup F v) (Z F v) (Q F v) ∧
    HasNaturalCenter (graphLocalGroup F w) (Z F w) (Q F w) := by
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans (eSL i).symm
  apply reduced_distance_bound_of_actor_models h
    (graph_actor_models_of_linear (reduced_triple h) K eG) ?_ hc hne
  intro x y hxy
  exact reduced_linear_graph_core_obstruction h (e false) (e true) y x hxy.symm

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

private def actorQuotientMarking {P : Fin 2 → Subgroup G} {v : Vertex (family P)}
    {E : Subgroup G} (c : LocalRankOneData (stabilizer (family P) v) E)
    (hs : c.Pstar = graphLocalGroup (family P) v)
    [((Q (family P) v).subgroupOf c.Pstar).Normal]
    {k : Type*} [Field k]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,k)) :
    (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar) ≃* SL(2,k) := by
  have hcore : (Q (family P) v).subgroupOf c.Pstar = pCore 2 c.Pstar := by
    rw [show Q (family P) v = c.Pstar.pCoreIn 2 from c.same_core.symm]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  let f := MulEquiv.subgroupCongr hs
  exact (QuotientGroup.quotientMulEquivOfEq hcore).trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e)

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- Equality holds for the defining fields in the original quotient markings themselves. -/
theorem reduced_linear_critical_field_orders (h : HypothesisF11 L₀ S₀)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L₀ i ⧸ pCore 2 (family L₀ i)) ≃* PSL(2,K i))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    Nat.card (K v.type) = Nat.card (K w.type) := by
  let ht := reduced_triple h
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans (eSL i).symm
  let hm := graph_actor_models_of_linear ht K eG
  let d := graphActorLocalData ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm
  have hd (x y : Vertex F) (he : (graph F).Adj x y) :
      (d x y he).Pstar = graphLocalGroup F x :=
    graphActorLocalData_star ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm x y he
  have hvw : v ≠ w := by
    intro hh
    have hp := source_b_positive ht
    have hdist := hc.1
    rw [hh,SimpleGraph.dist_self] at hdist
    omega
  obtain ⟨a,hva,_⟩ := exists_predecessor F ht.generate w v hvw.symm
  obtain ⟨z,hwz,_⟩ := exists_predecessor F ht.generate v w hvw
  let c₀ := d v a hva
  let c₁ := d w z hwz
  have ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v) := by
    rw [show c₀.Pstar = graphLocalGroup F v from hd v a hva]
    exact graph_actor_odd_index ht v
  have ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w) := by
    rw [show c₁.Pstar = graphLocalGroup F w from hd w z hwz]
    exact graph_actor_odd_index ht w
  let := graph_local_core_normal v c₀
  let := graph_local_core_normal w c₁
  let : ((Q F v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
  let : ((Q F w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
  let := graph_Z_elementary ht v
  let := graph_Z_elementary ht w
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  let : ((Q (reducedFamily L₀ S₀) v).subgroupOf c₀.Pstar).Normal := graph_local_core_normal v c₀
  let : ((Q (reducedFamily L₀ S₀) w).subgroupOf c₁.Pstar).Normal := graph_local_core_normal w c₁
  let : IsElementaryAbelian 2 (Z (reducedFamily L₀ S₀) v) := graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z (reducedFamily L₀ S₀) w) := graph_Z_elementary ht w
  obtain ⟨σ₀,σ₁,s₀,s₁,_,_,hn,_,_⟩ :=
    reduced_natural_endpoint_sections_exists h hc hne _ _ c₀ c₁ ho₀ ho₁
  let f₀ := actorQuotientMarking c₀ (hd v a hva) (source_linear_quotient_at ht K eG v)
  let f₁ := actorQuotientMarking c₁ (hd w z hwz) (source_linear_quotient_at ht K eG w)
  obtain ⟨T₀⟩ := Sylow.nonempty (p := 2) (G := c₀.Pstar ⧸ (Q F v).subgroupOf c₀.Pstar)
  obtain ⟨T₁⟩ := Sylow.nonempty (p := 2) (G := c₁.Pstar ⧸ (Q F w).subgroupOf c₁.Pstar)
  exact (quotient_sylow_omega_card f₀ T₀).symm.trans
    ((hn.sylow_omega_card_eq T₀ T₁).trans (quotient_sylow_omega_card f₁ T₁))

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The assembled linear Chapter 7 branch, retaining both natural centers
and equality of the actual original field orders. -/
theorem reduced_linear_noncommuting_distance_and_fields (h : HypothesisF11 L₀ S₀)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L₀ i ⧸ pCore 2 (family L₀ i)) ≃* PSL(2,K i))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    HasNaturalCenter (graphLocalGroup F v) (Z F v) (Q F v) ∧
    HasNaturalCenter (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Nat.card (K v.type) = Nat.card (K w.type) := by
  have hb := reduced_linear_noncommuting_distance_bound h K e hc hne
  exact ⟨hb.1,hb.2.1,hb.2.2,reduced_linear_critical_field_orders h K e hc hne⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
