module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.DistanceBoundSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs

/-!
# Transporting the actual odd-index local actors into the Chapter 7 bound

An odd-index normal actor contains the full edge two-core, so its Chapter 6
enlargement is itself. Sylow generation identifies it with the intrinsic
local graph actor. This proves covariance and transports the actual 6.2(c)
dichotomy, restricting its Sylow from the full stabilizer centralizer when
necessary. The constructed endpoint natural sections then prove both
Chapter 7 distance branches on this same graph.

The final application still requires the actual rank-one data with odd
indices, the 6.5 adjacent-core obstruction, and the model branching orders.
No representation, natural-section, faithfulness, residual-fixed-space,
Sylow-product, covariance or center-dichotomy premise is left in that interface.
Their source instantiation and the Chapter 10 assembly remain open.

Source: DGS, *Groups and Graphs* (1985), (6.1)--(6.2), pp.118–119,
(6.5)--(6.7), pp.121–123, and (7.1)--(7.5), pp.126–131.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

private theorem sylow_restrict_overgroup (Q K H : Subgroup G)
    (hQK : Q ≤ K) (hKH : K ≤ H) (hQH : Stellmacher.IsSylowSubgroupIn Q H) :
    Stellmacher.IsSylowSubgroupIn Q K := by
  obtain ⟨T,hT⟩ := hQH
  have hTr : (T : Subgroup H) ≤ (inclusion hKH).range := by
    intro t ht
    refine ⟨⟨t,hQK (hT ▸ mem_map_of_mem H.subtype ht)⟩,?_⟩
    rfl
  let S := T.comapOfInjective (inclusion hKH) (inclusion_injective _) hTr
  refine ⟨S,?_⟩
  rw [←hT]
  ext x
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨inclusion hKH k,hk,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨⟨t,hQK (hT ▸ mem_map_of_mem H.subtype ht)⟩,ht,rfl⟩

/-- Odd index makes the chosen actor equal to the literal full-edge-core enlargement. -/
theorem localEnlargement_eq_star_of_odd_index {P E : Subgroup G}
    (c : LocalRankOneData P E) (ho : ¬ 2 ∣ c.Pstar.relIndex P) :
    localEnlargement c = c.Pstar := by
  apply sup_eq_left.mpr
  exact local_twoGroup_le_star c ho _ (isPGroup_pCoreIn 2 E)
    ((pCoreIn_le 2 E).trans (le_sup_right.trans c.supplement.le))

/-- Identify the supplied odd-index edge actor with the intrinsic source graph actor. -/
theorem graph_odd_local_actor_eq {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w)
    (c : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) w))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v)) :
    c.Pstar = graphLocalGroup (family P) v := by
  exact (localEnlargement_eq_star_of_odd_index c ho).symm.trans
    (localEnlargement_eq_sylowGenerated c (source_edge_core_sylow h hB he)
      (source_edge_vertex_sylow h hS he))

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- Transport the actual 6.2(c) dichotomy to the supplied odd-index actor. -/
theorem reduced_odd_local_actor_dichotomy (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (he : (graph F).Adj v w)
    (c : LocalRankOneData (stabilizer F v) (stabilizer F v ⊓ stabilizer F w))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F v)) :
    Stellmacher.IsSylowSubgroupIn (Q F v)
      (c.Pstar ⊓ centralizer (Z F v : Set (G₀ L₀ S₀))) ∨
    Z F v = Stellmacher.omegaOneCenterAmbient c.Pstar := by
  let ht := reduced_triple h
  rcases reduced_centralizer_sylow_or_Z_eq h he with hs | hs
  · exact Or.inl (sylow_restrict_overgroup _ _ _
      (le_inf (source_core_le_star c) (graph_Q_centralizes_Z ht v))
      (inf_le_inf_right _ c.Pstar_le) hs)
  · obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) he
    have hh := source_center_eq_enlargement_omega_of_seed c
      (source_edge_core_sylow ht (reduced_borel_core_sylow h) he) ⟨T,hT⟩ T (hs T)
    rw [localEnlargement_eq_star_of_odd_index c ho] at hh
    exact Or.inr hh

/-- The local graph transports and center dichotomy require no separate callbacks.
The remaining hypotheses are actual rank-one actors, odd indices, 6.5 and branching. -/
theorem reduced_noncommuting_distance_bound_of_odd_localData
    (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x) (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤
      normalizer ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hbranch : ∀ i, ∃ k, ((F (!i)).subgroupOf (F i)).index - 1 = 2^k) :
    (b F = 1 ∨ b F = 2) ∧
    HasNaturalCenter (L v) (Z F v) (Q F v) ∧
    HasNaturalCenter (L w) (Z F w) (Q F w) := by
  let ht := reduced_triple h
  have hn (x : Vertex F) : ∃ y, (graph F).Adj x y := by
    obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F x
    refine ⟨g • base F (!x.type),?_⟩
    rw [←hg]
    exact (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr
      ⟨by change x.type ≠ !x.type; cases x.type <;> decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hactual (x : Vertex F) : L x = graphLocalGroup F x := by
    obtain ⟨y,he⟩ := hn x
    rw [←hstar x y he]
    exact graph_odd_local_actor_eq ht (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) he (d x y he) (by rw [hstar]; exact hodd x)
  have hdich (x : Vertex F) : Stellmacher.IsSylowSubgroupIn (Q F x)
      (L x ⊓ centralizer (Z F x : Set (G₀ L₀ S₀))) ∨
      Z F x = Stellmacher.omegaOneCenterAmbient (L x) := by
    obtain ⟨y,he⟩ := hn x
    simpa only [hstar] using reduced_odd_local_actor_dichotomy h he (d x y he)
      (by rw [hstar]; exact hodd x)
  apply reduced_noncommuting_distance_bound_of_localData h L
    (fun x => by rw [hactual]; exact sylowGenerated_le _) ?_ d hstar hodd hdich hob hc hne hbranch
  intro g x
  rw [hactual,hactual]
  exact graphLocalGroup_conjugate ht g x

/-- Canonical graph-actor application: the edge data supply actor identification,
so no choice of a covariant actor family is an additional premise. -/
theorem reduced_noncommuting_distance_bound_of_graph_localData
    (h : HypothesisF11 L₀ S₀)
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x) (stabilizer F x ⊓ stabilizer F y))
    (hodd : ∀ x y he, ¬ 2 ∣ (d x y he).Pstar.relIndex (stabilizer F x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤
      normalizer ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hbranch : ∀ i, ∃ k, ((F (!i)).subgroupOf (F i)).index - 1 = 2^k) :
    (b F = 1 ∨ b F = 2) ∧
    HasNaturalCenter (graphLocalGroup F v) (Z F v) (Q F v) ∧
    HasNaturalCenter (graphLocalGroup F w) (Z F w) (Q F w) := by
  have hstar (x y : Vertex F) (he : (graph F).Adj x y) :
      (d x y he).Pstar = graphLocalGroup F x :=
    graph_odd_local_actor_eq (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) he (d x y he) (hodd x y he)
  apply reduced_noncommuting_distance_bound_of_odd_localData h (graphLocalGroup F)
    d hstar ?_ hob hc hne hbranch
  intro x
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F x
  have he : (graph F).Adj x (g • base F (!x.type)) := by
    rw [←hg]
    exact (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr
      ⟨by change x.type ≠ !x.type; cases x.type <;> decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩
  rw [←hstar x _ he]
  exact hodd x _ he

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
