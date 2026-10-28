module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.SourceConclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneActionSource

/-!
# Constructing the b=1 Chapter 10 action and original natural cores

The Chapter 7 natural sections and sharp reciprocal indices supply the
literal neighbor-center Sylow image. Restricting an edge Sylow to the actual
actor proves fixed-space generation on that same section. Both center/core
products are the full edge two-core, giving the core-cover field of the
existing Chapter 10 action interface without a separate premise.

A common-edge conjugator transports an arbitrary distance-one noncommuting
critical pair to the two base vertices, with reversal when needed. Applying
Chapter 10's existing paired-action theorems then proves that the original
full parabolic cores are elementary and constructs their natural quotients
by the full embedded actor centers. The original inclusion and the actual
matrix markings are retained throughout.

Only the genuine actor-model input remains in the general construction.
The full-catalogue application discharges it except for the still-unproved
order-144 enlargement exclusion owned by setup. No Chapter 10 classification
is assumed, and the unconditional Chapter 7 source theorem remains open.
Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126--127,
(10.4)--(10.5)(a,b), pp.155--156, and the reduction pp.95--96;
Aschbacher--Smith, F.1.9, pp.261--262.
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

/-- Construct the b=1 Chapter 10 action from the recognized literal critical sections. -/
theorem reduced_bOne_center_action_exists (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (he : (graph F).Adj v w) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra (ZMod 2) k),
      ∃ c : BOneActionData F v w k (Fin 2 → k),
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
  have hQw : Q F w ≤ L := pGroup_le_sylowGenerated _ _
    ((source_Z_Q_U ht w).2.trans ((ballKernel_one_le_edge F he.symm).trans inf_le_right))
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
  have hZwQw : Z F w ≤ Q F w := (source_Z_Q_U ht w).1.trans (map_subtype_le _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) he
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
          _ _ inf_le_left (source_edge_core_sylow ht (reduced_borel_core_sylow h) he) T hT]
        have hzQ := graph_Q_le_edgeCore ht he.symm (hZwQw hz)
        change (z : G₀ L₀ S₀) ∈ (stabilizer F w ⊓ stabilizer F v).pCoreIn 2 at hzQ
        rw [inf_comm] at hzQ
        exact hzQ
      rw [←hT'] at hzS
      obtain ⟨a,ha,he⟩ := hzS
      exact (Subtype.ext he : a = z) ▸ ha
    exact (R.is_maximal' (T'.isPGroup'.map π) hRT).symm
  have hspan : Z F v = sylowCenterSpan L := by
    have hh := local_center_span _ _ (d v w he) (by rw [hd]; exact ho v)
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
  have hQvE : Q F v ≤ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 := graph_Q_le_edgeCore ht he
  have hQwE : Q F w ≤ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 := by
    simpa only [inf_comm] using graph_Q_le_edgeCore ht he.symm
  have hproduct : Z F v ⊔ Q F w = (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 :=
    sylow_join_eq_of_le (stabilizer F w) (Z F v) (Q F w) _ hs₁
      (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans inf_le_right)
      (((source_Z_Q_U ht v).1.trans (map_subtype_le _)).trans hQvE) hQwE
  refine ⟨k,inferInstance,inferInstance,inferInstance,inferInstance,{
    adjacent := he
    actor := L
    actor_le := sylowGenerated_le _
    core_le := hQ
    neighbor_core_le := hQw
    supplement := graphLocalGroup_sup_edge ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) he
    sylow := T
    sylow_le_actor := sylow_le_sylowGenerated _ T
    quotient := π
    onto := hπ
    kernel := hker
    representation := N
    coordinates := s
    imageSylow := R
    neighbor_image := hR.symm
    core_cover := hQvE.trans hproduct.ge
    centralizer_intersection := hi.2.2
    sharp_index := hsharp
    quadratic := hquad
    generated := hgenerated
    fixed_bot := hfixed },rfl⟩

/-- Move a distance-one critical pair to the two original base vertices,
retaining its noncommutation and allowing reversal of the vertex types. -/
theorem reduced_bOne_base_critical_noncommuting (h : HypothesisF11 L₀ S₀)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    IsCriticalPair F (base F false) (base F true) ∧
      ⁅Z F (base F false),Z F (base F true)⁆ ≠ ⊥ := by
  let := finite_endpoints (reduced_triple h)
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have he : (graph F).Adj v w := SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
  obtain ⟨g,hv,hw⟩ := incident_common_translate F he.2
  have htype : w.type = !v.type := Bool.eq_not_of_ne he.1.symm
  rw [htype] at hw
  have hadj : (graph F).Adj (base F v.type) (base F (!v.type)) :=
    ⟨by change v.type ≠ !v.type; cases v.type <;> decide,
      Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcbase : IsCriticalPair F (base F v.type) (base F (!v.type)) := by
    refine ⟨(SimpleGraph.dist_eq_one_iff_adj.mpr hadj).trans hb.symm,?_⟩
    intro hle
    apply hc.2
    rw [←hv,←hw,Z_translate,U_translate]
    exact map_mono hle
  have hnebase : ⁅Z F (base F v.type),Z F (base F (!v.type))⁆ ≠ ⊥ := by
    intro hh
    apply hne
    rw [←hv,←hw,Z_translate,Z_translate,←map_commutator,hh,Subgroup.map_bot]
  cases hvtype : v.type
  · simpa only [hvtype,Bool.not_false] using And.intro hcbase hnebase
  · have hcback := (reduced_noncommuting_critical_intersections h hcbase hnebase).1
    have hneback : ⁅Z F (base F (!v.type)),Z F (base F v.type)⁆ ≠ ⊥ := by
      rwa [commutator_comm]
    simpa only [reducedFamily,hvtype,Bool.not_true] using And.intro hcback hneback

/-- Construct both marked b=1 actions and apply the existing Chapter 10
consumer to the literal original full parabolic cores. -/
theorem original_bOne_natural_cores_of_actor_models (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    IsElementaryAbelian 2 ((parabolic L₀ S₀ 0).pCoreIn 2) ∧
    IsElementaryAbelian 2 ((parabolic L₀ S₀ 1).pCoreIn 2) ∧
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BOneActionData F (base F false) (base F true) k₀ (Fin 2 → k₀))
        (c₁ : BOneActionData F (base F true) (base F false) k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F (base F false) ∧
        c₁.actor = graphLocalGroup F (base F true) ∧ Nat.card k₀ = Nat.card k₁ ∧
        OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ := by
  obtain ⟨hcbase,hnebase⟩ := reduced_bOne_base_critical_noncommuting h hc hne hb
  have he : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,c₀,ha₀⟩ := reduced_bOne_center_action_exists h hm hcbase hnebase he
  have hcback := (reduced_noncommuting_critical_intersections h hcbase hnebase).1
  obtain ⟨k₁,f₁,n₁,ch₁,a₁,c₁,ha₁⟩ := reduced_bOne_center_action_exists h hm hcback
    (by rwa [commutator_comm]) he.symm
  have haeq₀ : a₀ = ZMod.algebra k₀ 2 := Subsingleton.elim _ _
  have haeq₁ : a₁ = ZMod.algebra k₁ 2 := Subsingleton.elim _ _
  subst a₀ a₁
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  have helem := original_cores_elementary_of_actions h c₀ c₁
  have hn := original_natural_cores_of_actions h c₀ c₁
    (LinearEquiv.refl (ZMod 2) _) (LinearEquiv.refl (ZMod 2) _)
  have hfields := paired_field_orders_eq (reduced_triple h) c₀ c₁ (LinearEquiv.refl (ZMod 2) _)
  exact ⟨helem.1,helem.2,k₀,f₀,n₀,ch₀,inferInstance,k₁,f₁,n₁,ch₁,inferInstance,
    c₀,c₁,ha₀,ha₁,hfields,hn.1,hn.2⟩

/-- Full-catalogue original b=1 natural-core application, retaining the outstanding enlargement premise. -/
theorem original_bOne_natural_cores_of_no_order144 (h : HypothesisF11 L₀ S₀)
    (hsmall : ∀ i : Fin 2,
      Nat.card (enlargedEndpoint L₀ S₀ i ⧸ pCore 2 (enlargedEndpoint L₀ S₀ i)) ≠ 144)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    IsElementaryAbelian 2 ((parabolic L₀ S₀ 0).pCoreIn 2) ∧
    IsElementaryAbelian 2 ((parabolic L₀ S₀ 1).pCoreIn 2) ∧
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BOneActionData F (base F false) (base F true) k₀ (Fin 2 → k₀))
        (c₁ : BOneActionData F (base F true) (base F false) k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F (base F false) ∧
        c₁.actor = graphLocalGroup F (base F true) ∧ Nat.card k₀ = Nat.card k₁ ∧
        OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ :=
  original_bOne_natural_cores_of_actor_models h (reduced_actor_models_of_no_order144 h hsmall)
    hc hne hb

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
