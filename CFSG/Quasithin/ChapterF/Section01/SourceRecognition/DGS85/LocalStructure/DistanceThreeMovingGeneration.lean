module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveFrattiniSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicMovingGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PredecessorNormality

/-!
# Distance-three moving-edge generation without an actor catalogue

The original predecessor-core image gives E normal in A normal in the
preceding Sylow image. In the exceptional quotient of order 144, if E has
order two this tower puts E in the Sylow Frattini subgroup. The normal
starred PSU₃(2) image has index two, so Frattini lies in that image. A common
involution there determines the whole Sylow. Equality of preceding and
moving edge cores contradicts the nonzero moving commutator, proving escape
and generation by V_beta and the full moving-edge Sylow.

All earlier-local inputs are supplied from the original F.1.1 hypothesis.
No enlarged rank-one catalogue, SD16 marking or local innerness is assumed.
Distance three remains an explicit hypothesis for this branch. Under the
unchanged general source assumptions, the final theorem restricts the
remaining order-144 alternative to critical distance at least five; it does
not prove the missing larger-distance normalization.

Source: DGS, *Groups and Graphs* (1985), 8.1(g), printed p.133,
with 5.1(c,d), pp.104--105, and the original 6.4--6.8 interfaces.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- At distance three the full neighboring span escapes every moving edge, including order 144. -/
theorem reduced_distance_three_span_escapes_moving_edge (h : HypothesisF11 L S)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : b F = 3) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (w : (graph F).neighborSet a') (hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥) :
    ¬ V F beta 1 ≤ stabilizer F a' ⊓ stabilizer F w.val := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  let M := graphLocalGroup F a'
  let D := M ⧸ pCore 2 M
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hmodel (hmod : IsRankOneModel D) :
      ¬ V F beta 1 ≤ stabilizer F a' ⊓ stabilizer F w.val :=
    source_span_escapes_moving_edge ht (reduced_borel_core_sylow h) d
      hc hab hd (by omega) hcomm hmod w hm
  have hnine : IsRankOneModel D ∨ (Nat.card D = 144 ∧
      ∃ N : Subgroup D, N.Normal ∧ IsElementaryAbelian 3 N ∧ Nat.card N = 9) :=
    reduced_graph_rankOne_or_normal_nine h a'
  have hprojective : IsRankOneModel D ∨ (Nat.card D = 144 ∧
      ∃ I : Subgroup D, I.Normal ∧ ClassicalGroup.IsPSU I 3 2 ∧ I.index = 2) :=
    reduced_graph_rankOne_or_projective_index_two h a'
  rcases hnine with hmod | ⟨hD,N,hN,hNE,h9⟩
  · exact hmodel hmod
  rcases hprojective with hmod | ⟨_,I,hI,hIM,hi⟩
  · exact hmodel hmod
  let := hN
  let := hNE
  let := hI
  by_cases hbig : 2 < (Q F a').relIndex (V F beta 1)
  · exact reduced_intrinsic_span_escapes_moving_edge h hc hab hd (by omega) hcomm w hm hbig
  obtain ⟨prev,hp,_,hVP,_,R,hR,hEA,hAS,hEN,hAN⟩ :=
    source_distance_three_predecessor_image_normality ht (reduced_borel_core_sylow h) d
      hc hab hd hb hcomm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (reduced_borel_core_sylow h) d w.property
  change Sylow 2 M at R T
  change (R : Subgroup M).map M.subtype = _ at hR
  change (T : Subgroup M).map M.subtype = _ at hT
  let Vb := V F beta 1
  let q := QuotientGroup.mk' (pCore 2 M)
  let E := (Vb.subgroupOf M).map q
  let A := ((Q F prev).subgroupOf M).map q
  let R' := quotientSylow R
  let T' := quotientSylow T
  change E ≤ A at hEA
  change A ≤ (R' : Subgroup D) at hAS
  change (E.subgroupOf A).Normal at hEN
  change (A.subgroupOf (R' : Subgroup D)).Normal at hAN
  let := hEN
  let := hAN
  let : IsElementaryAbelian 2 Vb := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) beta
  have hVR : Vb ≤ (R : Subgroup M).map M.subtype := by
    rw [hR]
    exact hVP.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore ht hp.symm)
  have hVM : Vb ≤ M := hVR.trans (map_subtype_le _)
  let : IsElementaryAbelian 2 (Vb.subgroupOf M) := IsElementaryAbelian.subgroupOf hVM
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hEcard : Nat.card E = (Q F a').relIndex Vb :=
    Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F a') Vb q
      (by rw [QuotientGroup.ker_mk']; exact (graph_intrinsic_core ht a').symm) hVM
  let : Finite Vb := Finite.of_injective (inclusion hVM) (inclusion_injective _)
  have hpos : (Q F a').relIndex Vb ≠ 0 := index_ne_zero_of_finite
  have hone : (Q F a').relIndex Vb ≠ 1 := by
    intro he
    exact hc.2 (((Z_neighbor_le_V F hab.symm).trans (relIndex_eq_one.mp he)).trans
      (source_Z_Q_U ht a').2)
  have htwo : Nat.card E = 2 := by change ¬ 2 < (Q F a').relIndex Vb at hbig; omega
  have hEf : E.subgroupOf (R' : Subgroup D) ≤ frattini R' :=
    Theory.GroupTheory.ambient_two_step_normal_order_two_le_frattini_of_normal_nine
      hD N h9 (pCore_quotient_pCore_eq_bot 2) R' A E hEA hAS htwo
  let : Finite ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S)) :=
    Finite.of_injective (inclusion (show stabilizer F a' ⊓ stabilizer F w.val ≤ stabilizer F a'
      from inf_le_left)) (inclusion_injective _)
  intro hVE
  have hVT : Vb ≤ (T : Subgroup M).map M.subtype := by
    rw [hT]
    exact pGroup_le_core_of_core_sylow _ Vb hVE (IsElementaryAbelian.isPGroup 2 Vb)
      (source_edge_core_sylow ht (reduced_borel_core_sylow h) w.property)
  have hET : E ≤ (T' : Subgroup D) := by
    apply map_mono
    intro x hx
    obtain ⟨y,hy,he⟩ := hVT hx
    exact (Subtype.ext he : y = x) ▸ hy
  have he : R' = T' := small_projective_normal_sylow_eq_of_frattini I hIM hi.le
    (pCore_quotient_pCore_eq_bot 2) R' T' E
    (by intro he; rw [he,card_bot] at htwo; omega) (hEA.trans hAS) hET hEf
  have hRT : R = T := by
    apply Sylow.ext
    have hh := congrArg (fun U : Sylow 2 D => (U : Subgroup D).comap q) he
    change ((R : Subgroup M).map q).comap q = ((T : Subgroup M).map q).comap q at hh
    rw [comap_map_eq,comap_map_eq] at hh
    rw [show q.ker = pCore 2 M from QuotientGroup.ker_mk' _] at hh
    have hQR : pCore 2 M ≤ (R : Subgroup M) := pCore_isPGroup.le_sylow_of_normal R
    have hQT : pCore 2 M ≤ (T : Subgroup M) := pCore_isPGroup.le_sylow_of_normal T
    rwa [sup_eq_left.mpr hQR,sup_eq_left.mpr hQT] at hh
  have hpw : prev = w.val := graph_intrinsic_edgeCore_unique_neighbor ht
    (reduced_borel_core_sylow h) hp w.property (by
      rw [←hR,hRT,hT]
      exact (pCoreIn_le 2 _).trans inf_le_right)
  apply hm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (inf_le_left.trans (hpw ▸ hVP)).trans (Noncommuting.graph_Q_centralizes_Z ht w.val)

/-- The original distance-three configuration satisfies source 8.1(g) without any model premise. -/
theorem reduced_distance_three_moving_edge_generation (h : HypothesisF11 L S)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : b F = 3) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (w : (graph F).neighborSet a') (hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥) :
    ∃ T : Sylow 2 ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S)),
      V F beta 1 ⊔ (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S))).map
        (stabilizer F a' ⊓ stabilizer F w.val).subtype = graphLocalGroup F a' := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) beta
  have hAP : V F beta 1 ≤ stabilizer F a' :=
    V_le_stabilizer_of_dist_add_le_b F ht.generate beta a' 1 hd.le
  have hesc : ¬ V F beta 1 ≤ stabilizer F w.val := fun hh =>
    reduced_distance_three_span_escapes_moving_edge h hc hab hd hb hcomm w hm (le_inf hAP hh)
  obtain ⟨T,hT⟩ := source_edge_core_sylow ht (reduced_borel_core_sylow h) w.property
  refine ⟨T,?_⟩
  rw [hT]
  exact graph_intrinsic_escaping_twoGroup_generates ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) w.property (V F beta 1) (IsElementaryAbelian.isPGroup 2 _) hAP hesc

/-- Under the original assumptions, the remaining order-144 exception has distance at least five. -/
theorem reduced_moving_edge_generation_or_long_order144 (h : HypothesisF11 L S)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (w : (graph F).neighborSet a') (hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥) :
    (∃ T : Sylow 2 ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S)),
      V F beta 1 ⊔ (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S))).map
        (stabilizer F a' ⊓ stabilizer F w.val).subtype = graphLocalGroup F a') ∨
      (5 ≤ b F ∧ (Q F a').relIndex (V F beta 1) = 2 ∧
        Nat.card (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')) = 144) := by
  by_cases hb3 : b F = 3
  · exact Or.inl (reduced_distance_three_moving_edge_generation h hc hab hd hb3 hcomm w hm)
  rcases reduced_moving_edge_generation_or_order144 h hc hab hd hb hcomm w hm with hg | he
  · exact Or.inl hg
  have ho := (source_critical_geometry (reduced_triple h) (reducedFullEarlierLocalTheorems h)
    hc hab hd hb hcomm).1
  obtain ⟨k,hk⟩ := ho
  exact Or.inr ⟨by omega,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
