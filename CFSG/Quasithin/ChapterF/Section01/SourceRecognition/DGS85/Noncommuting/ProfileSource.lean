module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LinearSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCenterAction
public import Theory.Representation.SL2NaturalOffenders.PairPointwiseFixer

/-!
# Constructing the literal Chapter 10 center and core actions

The two natural critical sections of (7.1) give reciprocal sharp indices.
The opposite-center image is therefore a Sylow subgroup of its actual SL₂
quotient. At distance two, that center lies in the intervening vertex core;
Sylow maximality makes this neighboring core have the same quotient image.
The edge Sylow gives fixed-space generation on this same natural section.

This constructs every field of Chapter 10's `BTwoCenterActionData`, including
the exact actor, quotient kernel and central section. Its existing opposite
lift theorem and `coreActionData` construction then produce the action used
for the literal Q/Z quotient. The general theorem retains only the earlier
actor-model input; two original linear markings discharge it in the final
application. No Chapter 10 profile classification is assumed or asserted.
Source: DGS, Groups and Graphs (1985), (7.1), pp.126--127,
and the input to (10.1)--(10.6), pp.154--158.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- Construct Chapter 10 center data from the recognized literal critical sections. -/
theorem reduced_bTwo_center_action_exists (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F v m w k (Fin 2 → k),
        c.actor = graphLocalGroup F v := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let d := graphActorLocalData ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm
  have hd (x y : Vertex F) (he : (graph F).Adj x y) :
      (d x y he).Pstar = graphLocalGroup F x :=
    graphActorLocalData_star ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm x y he
  have ho := graph_actor_odd_index ht
  obtain ⟨hn₀,hn₁,hs₀,hs₁⟩ := reduced_critical_natural_centers_of_localData h
    (graphLocalGroup F) d hd ho hc hne
  obtain ⟨k,_,_,_,π,hπ,hker,⟨s⟩⟩ := hn₀
  obtain ⟨k',_,_,_,π',hπ',hker',⟨s'⟩⟩ := hn₁
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  let : CharP k' 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k').injective 2
  let L := graphLocalGroup F v
  let L' := graphLocalGroup F w
  let N : Representation (ZMod 2) SL(2,k) (Fin 2 → k) := SL2NaturalOffenders.NoStrong.natural
  let N' : Representation (ZMod 2) SL(2,k') (Fin 2 → k') := SL2NaturalOffenders.NoStrong.natural
  let A := ((Z F w).subgroupOf L).map π
  let A' := ((Z F v).subgroupOf L').map π'
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite L' := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let := graph_Z_elementary ht v
  let := graph_Z_elementary ht w
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary ht v
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  let : Finite (Z F v) := Finite.of_injective (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let : Finite (Z F w) := Finite.of_injective (inclusion (Z_le_stabilizer F w)) (inclusion_injective _)
  have hi := reduced_noncommuting_critical_intersections h hc hne
  have hwL : Z F w ≤ L := pGroup_le_sylowGenerated _ _
    (criticalPair_centers F ht.generate hc).1 (IsElementaryAbelian.isPGroup 2 _)
  have hvL' : Z F v ≤ L' := pGroup_le_sylowGenerated _ _
    (criticalPair_centers F ht.generate hi.1).1 (IsElementaryAbelian.isPGroup 2 _)
  have hQ : Q F v ≤ L := pGroup_le_sylowGenerated _ _
    (pCoreIn_le 2 _) (isPGroup_pCoreIn 2 _)
  have hQm : Q F m ≤ L := pGroup_le_sylowGenerated _ _
    ((source_Z_Q_U ht m).2.trans ((ballKernel_one_le_edge F hvm.symm).trans inf_le_right))
    (isPGroup_pCoreIn 2 _)
  have hA : A ≠ ⊥ := by
    intro hz
    have he := (Subgroup.map_eq_bot_iff _).mp hz
    rw [hker] at he
    apply hne
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact (fun z hz => graph_Q_centralizes_Z ht v
      (he (show (⟨z,hwL hz⟩ : L) ∈ (Z F w).subgroupOf L from hz)))
  have hA' : A' ≠ ⊥ := by
    intro hz
    have he := (Subgroup.map_eq_bot_iff _).mp hz
    rw [hker'] at he
    apply hne
    rw [commutator_eq_bot_iff_le_centralizer]
    exact (fun z hz => graph_Q_centralizes_Z ht w
      (he (show (⟨z,hvL' hz⟩ : L') ∈ (Z F v).subgroupOf L' from hz)))
  have hp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z F w)).comap_subtype.map _
  have hp' : IsPGroup 2 A' := (IsElementaryAbelian.isPGroup 2 (Z F v)).comap_subtype.map _
  have hlow := SL2NaturalOffenders.marked_two_subgroup_card_le_fixed_quotient
    (MulEquiv.refl SL(2,k)) N (LinearEquiv.refl (ZMod 2) (Fin 2 → k))
    (fun _ _ => rfl) hA hp
  have hlow' := SL2NaturalOffenders.marked_two_subgroup_card_le_fixed_quotient
    (MulEquiv.refl SL(2,k')) N' (LinearEquiv.refl (ZMod 2) (Fin 2 → k'))
    (fun _ _ => rfl) hA' hp'
  have hr := reciprocal_section_indices L L' (Q F v) (Q F w) (Z F v) (Z F w)
    _ _ N π N' π' s s' hwL hvL' hker hker' hi.2.1 hi.2.2 hne hlow hlow'
  obtain ⟨_,R,hR⟩ := SL2NaturalOffenders.marked_sylow_of_fixed_quotient_le_card
    (MulEquiv.refl SL(2,k)) N (LinearEquiv.refl (ZMod 2) (Fin 2 → k))
    (fun _ _ => rfl) hA hp hr.2.2.1.le
  have hZwQm : Z F w ≤ Q F m := graph_Z_le_Q_of_short ht (reduced_kernel_sylow h)
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hmw.symm,hb]; decide)
  have hQimage : ((Q F m).subgroupOf L).map π = R := by
    exact R.is_maximal' ((isPGroup_pCoreIn 2 (stabilizer F m)).comap_subtype.map π)
      (by rw [hR]; exact map_mono (comap_mono hZwQm))
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) hvm
  obtain ⟨T',hT'⟩ := T.exists_map_subtype_eq_of_le (H := L)
    (sylowGenerated_le _) (sylow_le_sylowGenerated _ T)
  have hR' : (R : Subgroup SL(2,k)) = (T' : Subgroup L).map π := by
    have hRT : (R : Subgroup SL(2,k)) ≤ (T' : Subgroup L).map π := by
      rw [hR]
      apply map_mono
      intro z hz
      have hzS : (z : G₀ L₀ S₀) ∈
          (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype := by
        rw [Theory.GroupTheory.AmalgamGraph.sylow_image_eq_edge_core
          _ _ inf_le_left (source_edge_core_sylow ht (reduced_borel_core_sylow h) hvm) T hT]
        have hzQ := graph_Q_le_edgeCore ht hvm.symm (hZwQm hz)
        change (z : G₀ L₀ S₀) ∈ (stabilizer F m ⊓ stabilizer F v).pCoreIn 2 at hzQ
        rw [inf_comm] at hzQ
        exact hzQ
      rw [←hT'] at hzS
      obtain ⟨a,ha,he⟩ := hzS
      exact (Subtype.ext he : a = z) ▸ ha
    exact (R.is_maximal' (T'.isPGroup'.map π) hRT).symm
  have hspan : Z F v = sylowCenterSpan L := by
    have hh := local_center_span _ _ (d v m hvm) (by rw [hd]; exact ho v)
    rw [hd] at hh
    exact hh
  have hgenerated : GeneratedByFixedSpace N R := by
    rw [hR']
    exact BinaryConjugationSection.sylow_span_fixedSpace_generated L _ _ N π s T' hspan
  have hquad : IsQuadratic N R := by
    have hh := critical_sections_quadratic L L' (Z F v) (Z F w) _ _ N π N' π'
      s s' hwL hvL'
    rw [hR]
    exact hh.1
  have hfixed : fixedSpace N ⊤ = ⊥ := by
    apply bot_unique
    intro z hz
    exact SL2NaturalOffenders.natural_fixed_all_eq_zero z (fun g => hz ⟨g,mem_top g⟩)
  have hsharp : Nat.card ((Fin 2 → k) ⧸ fixedSpace N R) = (Q F w).relIndex (Z F v) := by
    rw [hR]
    exact hr.2.2.1.trans (hr.2.1.trans (actor_image_card_eq_relIndex L' (Q F w)
      (Z F v) π' hker' hvL'))
  refine ⟨k,inferInstance,inferInstance,inferInstance,inferInstance,{
    middle := hvm
    terminal := hmw
    actor := L
    actor_le := sylowGenerated_le _
    core_le := hQ
    neighbor_core_le := hQm
    critical_le := hwL
    factor := ?_
    sylow := T
    sylow_le_actor := sylow_le_sylowGenerated _ T
    quotient := π
    onto := hπ
    kernel := hker
    representation := N
    coordinates := s
    imageSylow := R
    critical_image := hR.symm
    neighbor_image := hQimage
    critical_product := hs₁
    centralizer_intersection := hi.2.2
    sharp_index := hsharp
    quadratic := hquad
    generated := hgenerated
    fixed_bot := hfixed },rfl⟩
  intro a ha
  simpa only [hd] using local_star_factor (d v m hvm) a ha

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- Apply the existing Chapter 10 opposite-lift and core-action consumers. -/
theorem reduced_bTwo_profile_action_exists (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v m w t : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w)
    (hvt : (graph F).Adj v t) (htne : t ≠ m) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F v m w k (Fin 2 → k),
        c.actor = graphLocalGroup F v ∧
        ∃ g : c.actor, (g : G₀ L₀ S₀) • m = t ∧
          c.quotient g ∉ normalizer (c.imageSylow : Set SL(2,k)) ∧
          Nonempty (BTwoActionData F w m v t k) := by
  obtain ⟨k,hfield,hfin,hchar,halg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h hm hc hne hb hvm hmw
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift (reduced_triple h) hvt htne
  exact ⟨k,hfield,hfin,hchar,halg,c,hactor,g,hg,hop,⟨c.coreActionData g hg⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- The original two linear markings supply the full Chapter 10 action data. -/
theorem reduced_linear_bTwo_profile_action_exists (h : HypothesisF11 L₀ S₀)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L₀ i ⧸ pCore 2 (family L₀ i)) ≃* PSL(2,K i))
    {v m w t : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w)
    (hvt : (graph F).Adj v t) (htne : t ≠ m) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F v m w k (Fin 2 → k),
        c.actor = graphLocalGroup F v ∧
        ∃ g : c.actor, (g : G₀ L₀ S₀) • m = t ∧
          c.quotient g ∉ normalizer (c.imageSylow : Set SL(2,k)) ∧
          Nonempty (BTwoActionData F w m v t k) := by
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eG (i : Bool) := (reduced_graphLinearQuotient h i (e i)).trans (eSL i).symm
  exact reduced_bTwo_profile_action_exists h
    (graph_actor_models_of_linear (reduced_triple h) K eG) hc hne hb hvm hmw hvt htne

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
