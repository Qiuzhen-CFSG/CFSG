module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceCommutingThree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceNoncommutingParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedLinearBetaProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation

/-!
# Critical selection for the literal L₂(8)/S₃ source pair

The original quotient markings give adjacent graph fields of orders eight and
two. Commuting critical distances above one would equate their quotient-Sylow
omega orders. At commuting distance one the linear field degrees would satisfy
3 = 2 or 1 = 6. Noncommuting distance one would equate the fields themselves.
Thus every critical pair is noncommuting at distance two. The positive field
power relation then places the binary endpoint first. Translate that same
critical edge to the reversed source base, retaining its full reduced groups.

Source: DGS, Groups and Graphs (1985), Chapters 8--11, pp.132--175;
Aschbacher--Smith F.1.12 and 14.2.16, pp.262--264,986.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCriticalGeometry
open ChapterF.Source ChapterF.Source.DGS85
open CommutingNontrivial CommutingTrivial
variable {G : Type*} [Group G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

/-- The original eight-field quotient marks every vertex of its own type. -/
theorem graph_linear_eight (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (v : Vertex F) (hv : v.type = false) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SL(2,GaloisField 2 3)) :=
  Assembly.linear_graph_quotient h false eK v hv

/-- The original cubic quotient marks every vertex of the opposite type. -/
theorem graph_linear_two (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) (hv : v.type = true) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SL(2,ZMod 2)) :=
  MixedDGS.graph_linear_two h eU v hv

private theorem graph_eight_model (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (v : Vertex F) (hv : v.type = false) :
    ClassicalGroup.IsPSL (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) 2 (2^3) :=
  ⟨GaloisField 2 3,inferInstance,inferInstance,GaloisField.card 2 3 (by decide),
    ⟨(graph_linear_eight h eK v hv).some.trans (Theory.PSL2.sl2QuotientEquiv _)⟩⟩

private theorem graph_two_model (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) (hv : v.type = true) :
    ClassicalGroup.IsPSL (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) 2 (2^1) :=
  ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨(graph_linear_two h eU v hv).some.trans (Theory.PSL2.sl2QuotientEquiv _)⟩⟩

private theorem graph_models (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) : IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) := by
  cases hv : v.type
  · exact .linear 3 (by decide) (graph_eight_model h eK v hv)
  · exact .linear 1 (by decide) (graph_two_model h eU v hv)

private theorem adjacent_quotient_omega_card_ne
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta : Vertex F} (hab : (graph F).Adj a beta)
    (Rα : Sylow 2 (graphLocalGroup F a)) (Rβ : Sylow 2 (graphLocalGroup F beta)) :
    Nat.card (omegaCenterIn ((Rα : Subgroup (graphLocalGroup F a)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup F a))))) ≠
    Nat.card (omegaCenterIn ((Rβ : Subgroup (graphLocalGroup F beta)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup F beta))))) := by
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
  let : ∀ v : Vertex F, Finite (graphLocalGroup F v) := fun v =>
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have height : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by decide)]
    norm_num
  have htwo : Nat.card (ZMod 2) = 2 := by norm_num [Nat.card_eq_fintype_card]
  have hbtype : beta.type = !a.type := Bool.eq_not_of_ne hab.1.symm
  cases ha : a.type with
  | false =>
    have hb : beta.type = true := by simpa only [ha,Bool.not_false] using hbtype
    have hα := (linear_marking_quotient_sylow_omega_card
      (graph_linear_eight h eK a ha).some Rα).trans height
    have hβ := (linear_marking_quotient_sylow_omega_card
      (graph_linear_two h eU beta hb).some Rβ).trans htwo
    omega
  | true =>
    have hb : beta.type = false := by simpa only [ha,Bool.not_true] using hbtype
    have hα := (linear_marking_quotient_sylow_omega_card
      (graph_linear_two h eU a ha).some Rα).trans htwo
    have hβ := (linear_marking_quotient_sylow_omega_card
      (graph_linear_eight h eK beta hb).some Rβ).trans height
    omega

/-- A commuting critical pair of the original eight-field/binary family has
distance one, retaining its directed critical pair and first path edge. -/
private theorem commuting_distance_one
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hcomm : ⁅Z F a,Z F a'⁆ = ⊥) : b F = 1 := by
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : ∀ v : Vertex F, Finite (graphLocalGroup F v) := fun v =>
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hp : 0 < b F := source_b_positive ht
  by_contra hb1
  have hb : 1 < b F := by omega
  let Rα : Sylow 2 (graphLocalGroup F a) := default
  let Rβ : Sylow 2 (graphLocalGroup F beta) := default
  apply adjacent_quotient_omega_card_ne h eK eU hab Rα Rβ
  by_cases htriv : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = ⊥
  · obtain ⟨_,k,hk,hkf,hkc,l,hl,hlf,hlc,hk2,hl2,ek,el⟩ :=
      reduced_critical_fields_two_from_chapterEight h (graph_models h eK eU)
        hc hab hd hb hcomm htriv
    let := hk
    let := hkf
    let := hkc
    let := hl
    let := hlf
    let := hlc
    exact ((linear_marking_quotient_sylow_omega_card el.some Rα).trans hl2).trans
      ((linear_marking_quotient_sylow_omega_card ek.some Rβ).trans hk2).symm
  · obtain ⟨w,hw,_⟩ := exists_moving_neighbor F
      (fun v => (source_Z_Q_U ht v).1) beta a' htriv
    have hcentral : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≤ Z F a' := by
      by_cases hwtype : w.val.type = false
      · exact reduced_linear_moving_commutator_central h (graph_models h eK eU)
          hc hab hd hb hcomm w hw (graph_linear_eight h eK w.val hwtype).some
      · exact reduced_linear_moving_commutator_central h (graph_models h eK eU)
          hc hab hd hb hcomm w hw
          (graph_linear_two h eU w.val (by cases ht : w.val.type <;> simp_all)).some
    obtain ⟨_,mid,_,_,hAD,hDI,hIN,_⟩ := reduced_critical_central_equivalences
      h (graph_models h eK eU) hc hab hd hb hcomm htriv
    have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
    exact reduced_natural_start_adjacent_parameter_equality h (graph_models h eK eU)
      hc hab hd hb hcomm htriv hnat Rα Rβ

private theorem commuting_one_false (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a b : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F b⁆ = ⊥) : False := by
  let d := Reduction.reducedFullEarlierLocalTheorems h
  have hadj := CommutingOneProfile.source_critical_one_adjacent hc hb
  have hbt : b.type = !a.type := Bool.eq_not_of_ne hadj.1.symm
  cases hat : a.type
  · have hbt' : b.type = true := by simpa only [hat,Bool.not_false] using hbt
    have hp := CommutingOneProfile.reduced_linear_linear_parameters h d hc hb hcomm
      3 1 (by decide) (by decide) (graph_eight_model h eK a hat) (graph_two_model h eU b hbt')
    omega
  · have hbt' : b.type = false := by simpa only [hat,Bool.not_true] using hbt
    have hp := CommutingOneProfile.reduced_linear_linear_parameters h d hc hb hcomm
      1 3 (by decide) (by decide) (graph_two_model h eU a hat) (graph_eight_model h eK b hbt')
    omega

/-- Every critical pair of the literal original eight-field/binary pair is noncommuting. -/
theorem critical_noncommuting (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a a' : Vertex F} (hc : IsCriticalPair F a a') : ⁅Z F a,Z F a'⁆ ≠ ⊥ := by
  intro hcomm
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
  exact commuting_one_false h eK eU hc
    (commuting_distance_one h eK eU hc hab hd hcomm) hcomm

private theorem noncommuting_one_false (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {v w : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) (hb : b F = 1) : False := by
  obtain ⟨_,_,k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,hfields,_⟩ :=
    Noncommuting.Reduction.original_bOne_natural_cores_of_actor_models h
      (graph_models h eK eU) hc hne hb
  let := f₀
  let := n₀
  let := ch₀
  let := f₁
  let := n₁
  let := ch₁
  have height := MixedDGS.source_action_field_card h ha₀ c₀.quotient c₀.onto c₀.kernel
    (graph_linear_eight h eK (base F false) rfl).some
  have htwo := MixedDGS.source_action_field_card h ha₁ c₁.quotient c₁.onto c₁.kernel
    (graph_linear_two h eU (base F true) rfl).some
  rw [height,htwo] at hfields
  norm_num [GaloisField.card 2 3 (by decide),Nat.card_zmod] at hfields

/-- The original pair itself has critical distance two; no critical witness is assumed. -/
theorem critical_distance_two (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) : DGS85.b F = 2 := by
  obtain ⟨a,a',hc⟩ := source_exists_criticalPair (Reduction.reduced_triple h)
  have hn := critical_noncommuting h eK eU hc
  exact (Reduction.reduced_intrinsic_noncommuting_bound h hc hn).resolve_left
    (fun hb => noncommuting_one_false h eK eU hc hn hb)

/-- The actual critical path starts at the binary type and crosses the eight-field type. -/
theorem critical_orientation (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {v m w : Vertex F} (hc : IsCriticalPair F v w)
    (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    v.type = true ∧ m.type = false := by
  have hne := critical_noncommuting h eK eU hc
  have hb := critical_distance_two h eK eU
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hcentral := Reduction.reduced_bTwo_middle_central h hc hne hb hvm hmw
  have hcomm := (Reduction.reduced_bTwo_center_identities h hc hne hb hvm hmw).2.2.2
  obtain ⟨k,f,n,ch,a,c,hactor⟩ :=
    Reduction.reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  let := f
  let := n
  let := ch
  have hv : v.type = true := by
    by_contra hv
    have hv' : v.type = false := Bool.eq_false_iff.mpr hv
    have hm : m.type = true := by
      have hh := hvm.1
      rw [hv'] at hh
      cases he : m.type <;> simp_all
    have hk := MixedDGS.source_action_field_card h hactor c.quotient c.onto c.kernel
      (graph_linear_eight h eK v hv').some
    have hval : 3 ≤ Nat.card ((graph F).neighborSet v) := by
      rw [card_neighbors_of_indices F
        (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
      exact source_valence_ge_three ht (Reduction.reduced_vertex_sylow h) v.type
    obtain ⟨t,htm,htne⟩ := Set.exists_ne_of_one_lt_ncard
      (s := (graph F).neighborSet v) (by rw [←Nat.card_coe_set_eq]; omega) m
    obtain ⟨r,hr,hpow⟩ := c.linear_core_field_power ht
      (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
      hb hactor hcentral htm htne hcomm.le
      (Reduction.reduced_graph_core_obstruction h v m hvm)
      (graph_linear_two h eU m hm).some
    rw [hk,GaloisField.card 2 3 (by decide),Nat.card_zmod] at hpow
    have hh : 8 ≤ 8^r := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ r by omega)
    norm_num at hpow
    omega
  refine ⟨hv,?_⟩
  have hh := hvm.1
  rw [hv] at hh
  cases he : m.type <;> simp_all


open Reduction

/-- Construct the binary-start critical pair at the reversed base edge, including its middle neighbor. -/
theorem reversed_base_critical
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    ∃ u : Vertex (reducedFamily ![U,K] S),
      IsCriticalPair (reducedFamily ![U,K] S) (base (reducedFamily ![U,K] S) false) u ∧
      ⁅Z (reducedFamily ![U,K] S) (base (reducedFamily ![U,K] S) false),
        Z (reducedFamily ![U,K] S) u⁆ ≠ ⊥ ∧
      (graph (reducedFamily ![U,K] S)).Adj (base (reducedFamily ![U,K] S) true) u := by
  have hpairs : ∃ a a' : Vertex F, IsCriticalPair F a a' :=
    source_exists_criticalPair (reduced_triple h)
  obtain ⟨a,a',hc⟩ := hpairs
  have hne := critical_noncommuting h eK eU hc
  have hb := critical_distance_two h eK eU
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let _ : ∀ i, Finite (swapFamily F i) := fun i => inferInstanceAs (Finite (F (!i)))
  have hdist : (graph F).dist a a' = 2 := hc.1.trans hb
  obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero (by rw [hdist]; decide)
  have hlen : p.length = 2 := hp.trans hdist
  let m := p.getVert 1
  have ham : (graph F).Adj a m := by
    simpa [m] using p.adj_getVert_succ (i := 0) (by omega)
  have hlast : p.getVert 2 = a' := by simpa [hlen] using p.getVert_length
  have hma' : (graph F).Adj m a' := by
    simpa [m,hlast] using p.adj_getVert_succ (i := 1) (by omega)
  obtain ⟨ha,hm⟩ := critical_orientation h eK eU hc ham hma'
  have hcs : IsCriticalPair (swapFamily F) (swapVertex F a) (swapVertex F a') := by
    constructor
    · simpa only [DGS85.swap_dist,DGS85.b_swapFamily] using hc.1
    · simpa only [DGS85.swap_Z,DGS85.swap_U] using hc.2
  have hns : ⁅Z (swapFamily F) (swapVertex F a),Z (swapFamily F) (swapVertex F a')⁆ ≠ ⊥ := by
    simpa only [DGS85.swap_Z] using hne
  have has : (graph (swapFamily F)).Adj (swapVertex F a) (swapVertex F m) :=
    (swapGraphIso F).map_adj_iff.mpr ham
  have hms : (graph (swapFamily F)).Adj (swapVertex F m) (swapVertex F a') :=
    (swapGraphIso F).map_adj_iff.mpr hma'
  obtain ⟨g,hga,hgm⟩ := incident_common_translate (swapFamily F) has.2
  rw [swapVertex_type,ha,Bool.not_true] at hga
  rw [swapVertex_type,hm,Bool.not_false] at hgm
  have hct := CommutingNontrivial.criticalPair_translate (swapFamily F) hcs g⁻¹
  have hnt : ⁅Z (swapFamily F) (g⁻¹ • swapVertex F a),
      Z (swapFamily F) (g⁻¹ • swapVertex F a')⁆ ≠ ⊥ := by
    rw [commuting_centers_translate]
    exact fun he => hns ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp he)
  have hmt := (Subgroup.CosetGeometry.translationGraphIso (swapFamily F) g⁻¹).map_adj_iff.mpr hms
  change (graph (swapFamily F)).Adj (g⁻¹ • swapVertex F m) (g⁻¹ • swapVertex F a') at hmt
  rw [←hga,inv_smul_smul] at hct hnt
  rw [←hgm,inv_smul_smul] at hmt
  unfold reducedFamily
  rw [pair_G₀_swap K U S]
  have hF : family (fun i => (P₀ ![U,K] S i).subgroupOf (G₀ ![K,U] S)) = swapFamily F := by
    funext i
    cases i
    · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![K,U] S)) (pair_P₀_swap K U S 0)
    · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![K,U] S)) (pair_P₀_swap K U S 1)
  rw [hF]
  exact ⟨g⁻¹ • swapVertex F a',hct,hnt,hmt⟩


end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCriticalGeometry
