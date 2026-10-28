module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalActorApplication

/-!
# Natural center actions at distance two without a catalogue premise

The actual critical endpoints are linear, with natural center sections and
both full-stabilizer Sylow products. Their reciprocal indices identify the
opposite-center image as an actual quotient Sylow. The intervening core
has the same image, and the intrinsic Sylow span proves fixed generation.
This constructs the literal Chapter 10 center and core actions without a
model hypothesis on the other vertex orbit or an order-144 exclusion.

Source: DGS, Groups and Graphs (1985), 7.1, pp.126--127, and the
center-action input to 10.1--10.6, pp.154--158.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- Construct Chapter 10 center data from the recognized literal critical sections. -/
theorem reduced_bTwo_center_action_exists (h : HypothesisF11 L₀ S₀)
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F v m w k (Fin 2 → k),
        c.actor = graphLocalGroup F v := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨d,hd⟩ := reduced_critical_actor_localData h hc hne hvm
  have ho : ¬ 2 ∣ d.Pstar.relIndex (stabilizer F v) := by
    rw [hd]
    exact graph_actor_odd_index ht v
  obtain ⟨hn₀,hn₁,hs₀,hs₁,_⟩ := reduced_critical_natural_centers_and_products h hc hne
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
    have hh := local_center_span _ _ d ho
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
  simpa only [hd,reducedFamily,L] using local_star_factor d a ha

/-- Both orientations have the same defining field and supply every existing
opposite-lift and literal core-action consumer at distance two. -/
theorem reduced_bTwo_equal_field_profile_actions (h : HypothesisF11 L₀ S₀)
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BTwoCenterActionData F v m w k₀ (Fin 2 → k₀))
        (c₁ : BTwoCenterActionData F w m v k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F v ∧ c₁.actor = graphLocalGroup F w ∧
        Nat.card k₀ = Nat.card k₁ ∧
        (∀ t, (graph F).Adj v t → t ≠ m →
          ∃ g : c₀.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₀.quotient g ∉ normalizer (c₀.imageSylow : Set SL(2,k₀)) ∧
            Nonempty (BTwoActionData F w m v t k₀)) ∧
        (∀ t, (graph F).Adj w t → t ≠ m →
          ∃ g : c₁.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₁.quotient g ∉ normalizer (c₁.imageSylow : Set SL(2,k₁)) ∧
            Nonempty (BTwoActionData F v m w t k₁)) := by
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,c₀,ha₀⟩ := reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  have hc' := (reduced_noncommuting_critical_intersections h hc hne).1
  obtain ⟨k₁,f₁,n₁,ch₁,a₁,c₁,ha₁⟩ := reduced_bTwo_center_action_exists h hc'
    (by rwa [commutator_comm]) hb hmw.symm hvm.symm
  have hi := (reduced_critical_natural_centers_and_products h hc hne).2.2.2.2
  have hk := (Noncommuting.Reduction.bTwo_center_action_field_order c₀).trans
    (hi.trans (Noncommuting.Reduction.bTwo_center_action_field_order c₁).symm)
  refine ⟨k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,hk,?_,?_⟩
  · intro t ht htm
    obtain ⟨g,hg,hout⟩ := c₀.exists_opposite_lift (reduced_triple h) ht htm
    exact ⟨g,hg,hout,⟨c₀.coreActionData g hg⟩⟩
  · intro t ht htm
    obtain ⟨g,hg,hout⟩ := c₁.exists_opposite_lift (reduced_triple h) ht htm
    exact ⟨g,hg,hout,⟨c₁.coreActionData g hg⟩⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
