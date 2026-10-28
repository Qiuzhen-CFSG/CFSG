module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicSylowSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEdgeGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveGraphApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration

/-!
# Terminal moving-edge generation with the precise small exception

Pass a common elementary subgroup of two full local Sylows through the
actual two-core quotient. The intrinsic separation theorem bounds its
image by two unless the Sylows coincide. If V_beta has larger image and
lies in the moving edge, the preceding and moving edge cores therefore
coincide. Their unique fixed neighbor contradicts the nonzero moving
commutator. The original starred overgroup theorem then generates the
whole terminal actor from V_beta and the full moving-edge Sylow.

The final original F.1.1 application combines this argument with the
existing Chapter 8 generation theorem on genuine enlarged rank-one
models. The only retained alternative has image order exactly two and
actual terminal quotient order 144. Thus no enlarged-model premise is
needed for the larger-image source branch. The remaining order-two
alternative, unrestricted 6.1 enlargement and general source assembly
are not claimed here. All cores, full-edge Sylows, and reduced-completion
inclusions retain their literal source meanings; the completion need
not be finite and the graph need not be a tree.
Source: DGS, Groups and Graphs (1985), 8.1(g), printed p.133,
using 5.1(c,d), pp.104--105, and 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- Two actual local Sylows with a common elementary subgroup are equal unless its core index is at most two. -/
theorem reduced_intrinsic_sylow_separation (h : HypothesisF11 L S) (v : Vertex F)
    (R T : Sylow 2 (graphLocalGroup F v)) (A : Subgroup (G₀ L S))
    [IsElementaryAbelian 2 A]
    (hAR : A ≤ (R : Subgroup (graphLocalGroup F v)).map (graphLocalGroup F v).subtype)
    (hAT : A ≤ (T : Subgroup (graphLocalGroup F v)).map (graphLocalGroup F v).subtype) :
    R = T ∨ (Q F v).relIndex A ≤ 2 := by
  let ht := reduced_triple h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 M)
  let E := (A.subgroupOf M).map q
  have hAM : A ≤ M := hAR.trans (map_subtype_le _)
  let : IsElementaryAbelian 2 (A.subgroupOf M) := IsElementaryAbelian.subgroupOf hAM
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hR : A.subgroupOf M ≤ R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hT : A.subgroupOf M ≤ T := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hAT hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hs := reduced_graph_quotient_sylow_separation h
  dsimp only [reducedFamily] at hs
  rcases @hs v (quotientSylow R) (quotientSylow T) E
      (inferInstance : IsElementaryAbelian 2 E) (map_mono hR) (map_mono hT) with he | he
  · left
    apply Sylow.ext
    have hh := congrArg (fun U : Sylow 2 (M ⧸ pCore 2 M) => (U : Subgroup _).comap q) he
    change ((R : Subgroup M).map q).comap q = ((T : Subgroup M).map q).comap q at hh
    rw [comap_map_eq,comap_map_eq] at hh
    rw [show q.ker = pCore 2 M from QuotientGroup.ker_mk' _] at hh
    have hQR : pCore 2 M ≤ (R : Subgroup M) := pCore_isPGroup.le_sylow_of_normal R
    have hQT : pCore 2 M ≤ (T : Subgroup M) := pCore_isPGroup.le_sylow_of_normal T
    rwa [sup_eq_left.mpr hQR,sup_eq_left.mpr hQT] at hh
  · right
    have hc : Nat.card E = (Q F v).relIndex A :=
      Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F v) A q
        (by rw [QuotientGroup.ker_mk']; exact (graph_intrinsic_core ht v).symm) hAM
    exact hc.symm.trans_le he

/-- A larger terminal image forces the original neighboring span to escape the full moving edge. -/
theorem reduced_intrinsic_span_escapes_moving_edge (h : HypothesisF11 L S)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (w : (graph F).neighborSet a') (hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥)
    (hbig : 2 < (Q F a').relIndex (V F beta 1)) :
    ¬ V F beta 1 ≤ stabilizer F a' ⊓ stabilizer F w.val := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  let M := graphLocalGroup F a'
  let A := V F beta 1
  obtain ⟨_,hb3,_,_,prev,hp,_,hAP,_⟩ := source_critical_geometry ht d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) beta
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (reduced_borel_core_sylow h) d hp
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (reduced_borel_core_sylow h) d w.property
  change Sylow 2 M at R T
  change (R : Subgroup M).map M.subtype = _ at hR
  change (T : Subgroup M).map M.subtype = _ at hT
  have hAR : A ≤ (R : Subgroup M).map M.subtype := by
    rw [hR]
    exact hAP.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore ht hp.symm)
  let : Finite ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S)) :=
    Finite.of_injective (inclusion (show stabilizer F a' ⊓ stabilizer F w.val ≤ stabilizer F a'
      from inf_le_left)) (inclusion_injective _)
  intro hAE
  have hAT : A ≤ (T : Subgroup M).map M.subtype := by
    rw [hT]
    exact pGroup_le_core_of_core_sylow _ A hAE (IsElementaryAbelian.isPGroup 2 A)
      (source_edge_core_sylow ht (reduced_borel_core_sylow h) w.property)
  have hRT : R = T := (reduced_intrinsic_sylow_separation h a' R T A hAR hAT).resolve_right
    (fun hi => (not_le_of_gt hbig) hi)
  have hpw : prev = w.val := graph_intrinsic_edgeCore_unique_neighbor ht
    (reduced_borel_core_sylow h) hp w.property (by
      rw [←hR,hRT,hT]
      exact (pCoreIn_le 2 _).trans inf_le_right)
  apply hm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (inf_le_left.trans (hpw ▸ hAP)).trans (Noncommuting.graph_Q_centralizes_Z ht w.val)

/-- The literal full-edge Sylow and V_beta generate the terminal actor when its core index exceeds two. -/
theorem reduced_intrinsic_moving_edge_generation (h : HypothesisF11 L S)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (w : (graph F).neighborSet a') (hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥)
    (hbig : 2 < (Q F a').relIndex (V F beta 1)) :
    ∃ T : Sylow 2 ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S)),
      V F beta 1 ⊔ (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S))).map
        (stabilizer F a' ⊓ stabilizer F w.val).subtype = graphLocalGroup F a' := by
  let ht := reduced_triple h
  let d := reducedFullEarlierLocalTheorems h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  have hb3 := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) beta
  have hAP : V F beta 1 ≤ stabilizer F a' :=
    V_le_stabilizer_of_dist_add_le_b F ht.generate beta a' 1 hd.le
  have hesc : ¬ V F beta 1 ≤ stabilizer F w.val := fun hh =>
    reduced_intrinsic_span_escapes_moving_edge h hc hab hd hb hcomm w hm hbig (le_inf hAP hh)
  obtain ⟨T,hT⟩ := source_edge_core_sylow ht (reduced_borel_core_sylow h) w.property
  refine ⟨T,?_⟩
  rw [hT]
  exact graph_intrinsic_escaping_twoGroup_generates ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) w.property (V F beta 1) (IsElementaryAbelian.isPGroup 2 _) hAP hesc

private theorem reduced_moving_edge_generation_or_index_two (h : HypothesisF11 L S)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (w : (graph F).neighborSet a') (hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥) :
    (∃ T : Sylow 2 ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S)),
      V F beta 1 ⊔ (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S))).map
        (stabilizer F a' ⊓ stabilizer F w.val).subtype = graphLocalGroup F a') ∨
      (Q F a').relIndex (V F beta 1) = 2 := by
  by_cases hbig : 2 < (Q F a').relIndex (V F beta 1)
  · exact Or.inl (reduced_intrinsic_moving_edge_generation h hc hab hd hb hcomm w hm hbig)
  right
  let ht := reduced_triple h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  have hAP : V F beta 1 ≤ stabilizer F a' :=
    V_le_stabilizer_of_dist_add_le_b F ht.generate beta a' 1 hd.le
  let : Finite (V F beta 1) := Finite.of_injective (inclusion hAP) (inclusion_injective _)
  have hpos : (Q F a').relIndex (V F beta 1) ≠ 0 := index_ne_zero_of_finite
  have hone : (Q F a').relIndex (V F beta 1) ≠ 1 := by
    intro he
    exact hc.2 (((Z_neighbor_le_V F hab.symm).trans (relIndex_eq_one.mp he)).trans
      (source_Z_Q_U ht a').2)
  omega

private theorem graph_model_or_order144 (h : HypothesisF11 L S) (v : Vertex F) :
    IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ∨
      Nat.card (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) = 144 := by
  have hb (j : Bool) :
      IsRankOneModel (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)) ∨
        Nat.card (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)) = 144 := by
    cases j
    · exact reduced_enlargement_rankOne_or_order144 h 0
    · exact reduced_enlargement_rankOne_or_order144 h 1
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let M := graphLocalGroup F (base F v.type)
  have heq : M.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : M ≃* graphLocalGroup F v :=
    (M.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    (reduced_graphEnlargementQuotient h v.type)
  rcases hb v.type with hm | hc
  · exact Or.inl (hm.of_equiv e)
  · exact Or.inr ((Nat.card_congr e.toEquiv).trans hc)

/-- The only remaining exception to source 8.1(g) has exact actor index two and actual quotient order 144. -/
theorem reduced_moving_edge_generation_or_order144 (h : HypothesisF11 L S)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a,Z F a'⁆ = ⊥)
    (w : (graph F).neighborSet a') (hm : ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥) :
    (∃ T : Sylow 2 ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S)),
      V F beta 1 ⊔ (T : Subgroup ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup (G₀ L S))).map
        (stabilizer F a' ⊓ stabilizer F w.val).subtype = graphLocalGroup F a') ∨
      ((Q F a').relIndex (V F beta 1) = 2 ∧
        Nat.card (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')) = 144) := by
  rcases graph_model_or_order144 h a' with hmodel | hcard
  · left
    exact source_moving_edge_generation (reduced_triple h) (reduced_borel_core_sylow h)
      (reducedFullEarlierLocalTheorems h) hc hab hd hb hcomm hmodel w hm
  · rcases reduced_moving_edge_generation_or_index_two h hc hab hd hb hcomm w hm with hg | hi
    · exact Or.inl hg
    · exact Or.inr ⟨hi,hcard⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
