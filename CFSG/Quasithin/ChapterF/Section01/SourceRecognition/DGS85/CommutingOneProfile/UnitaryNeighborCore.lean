module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryRemoteLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborCoreCenter

/-!
# The unitary neighboring-core intersection and center index

The three-edge remote-layer argument makes I_beta disjoint from the
opposite beta core and hence elementary. The same three-edge walk gives
the full edge supplement at that opposite vertex. The rank-one omega
calculation then covers both I_beta and Z_alpha by Z_beta Q_beta'.
Disjointness proves I_beta = Z_beta and identifies the order of Z_beta
with the original critical-center index.

The final theorem constructs its own escaping turn from the beta marking.
Neither a path action nor an escape witness is an additional hypothesis.
Both unitary covers and every positive fixed-field degree are retained.
Source: DGS85, Groups and Graphs, (11.6)(a,c), pp.172--174.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem normalizes_join_of_displacement (A N T : Subgroup G)
    (hn : T ≤ normalizer (N : Set G)) (hc : ⁅T,A⁆ ≤ N) :
    T ≤ normalizer ((A ⊔ N : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  have ha : A ≤ (A ⊔ N).comap (MulAut.conj t).toMonoidHom := by
    intro a ha
    change t*a*t⁻¹ ∈ A ⊔ N
    have hh := (A ⊔ N).mul_mem (mem_sup_right (hc (commutator_mem_commutator ht ha)))
      (mem_sup_left ha)
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hN : N ≤ (A ⊔ N).comap (MulAut.conj t).toMonoidHom := by
    intro n hn'
    exact mem_sup_right (le_normalizer_iff.mp hn t ht n hn')
  exact (sup_le ha hN) hx

private theorem elementary_edge_cover
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (M : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (A C K : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 C]
    (hAS : A ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)
    (hCS : C ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)
    (hK : K ≤ stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔ K =
      stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hKA : K ≤ normalizer (A : Set G)) (hne : ¬ A ≤ Q (family P) a) :
    C ≤ A ⊔ Q (family P) a := by
  let := finite_endpoints h
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let S := E.pCoreIn 2
  let W := A ⊔ Q (family P) a
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  have hAL : A ≤ L := hAS.trans (hT ▸ map_subtype_le _)
  have hCL : C ≤ L := hCS.trans (hT ▸ map_subtype_le _)
  have hAT : A.subgroupOf L ≤ (T : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hT.symm ▸ hAS hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hCT : C.subgroupOf L ≤ (T : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hT.symm ▸ hCS hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hdisp : ⁅S,A⁆ ≤ Q (family P) a := by
    have hh := elementary_actor_displacement_le_kernel L q
      (QuotientGroup.mk'_surjective _) M T A hAL (hT.symm ▸ hAS)
    rw [hT,QuotientGroup.ker_mk'] at hh
    exact hh.trans_eq (localGroup_core_eq (family P) d a)
  have hSW : S ≤ normalizer (W : Set G) := normalizes_join_of_displacement A _ S
    ((pCoreIn_le 2 E).trans (inf_le_left.trans (stabilizer_normalizes_Q _ a))) hdisp
  have hKW : K ≤ normalizer (W : Set G) :=
    (le_inf hKA (hK.trans (inf_le_left.trans (stabilizer_normalizes_Q _ a)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hEW : E ≤ normalizer (W : Set G) := by
    change S ⊔ K = E at hcover
    rw [←hcover]
    exact sup_le hSW hKW
  have hNW : normalizer (T : Set L) ≤ normalizer (W.subgroupOf L : Set L) := by
    rw [←(source_edge_local_normalizer h d hab M T hT).2]
    intro x hx
    exact le_normalizer_comap L.subtype (hEW ⟨d.local_le a x.property,hx⟩)
  have hne' : (A.subgroupOf L).map q ≠ ⊥ := by
    intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hh
    have hm := map_mono (f := L.subtype) hh
    rw [map_subgroupOf_eq_of_le hAL] at hm
    exact hne (hm.trans_eq (localGroup_core_eq (family P) d a))
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 (C.subgroupOf L) := IsElementaryAbelian.subgroupOf hCL
  let : IsElementaryAbelian 2 ((C.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hOmega := source_rank_one_elementary_le_sylow_omega M
    (T.mapSurjective (QuotientGroup.mk'_surjective _)) ((C.subgroupOf L).map q) (map_mono hCT)
  have hpre := source_rank_one_omega_preimage q (QuotientGroup.mk'_surjective _) M T
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal T)
    (A.subgroupOf L) hAT hne'
  have hCpre := (Subgroup.map_le_iff_le_comap).mp hOmega
  rw [hpre] at hCpre
  have hkerW : q.ker ≤ W.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hh : (x : G) ∈ Q (family P) a := by
      rw [←localGroup_core_eq (family P) d a]
      exact mem_map_of_mem L.subtype hx
    exact mem_sup_right hh
  have hCW := hCpre.trans (sup_le
    (conjugateSpanBy_le (comap_mono le_sup_left) hNW) hkerW)
  intro x hx
  exact hCW (show (⟨x,hCL hx⟩ : L) ∈ C.subgroupOf L from hx)

private def translated_quotient (d : EarlierLocalTheorems (family P))
    (a : Vertex (family P)) (g : G) :
    (d.localGroup (g • a) ⧸ pCore 2 (d.localGroup (g • a))) ≃*
      (d.localGroup a ⧸ pCore 2 (d.localGroup a)) := by
  let e := (MulEquiv.subgroupCongr (d.conjugate g a)).trans
    ((d.localGroup a).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  exact QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private theorem core_sup_index (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : Q.relIndex (Q ⊔ C) = Q.relIndex C := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Q.le_normalizer hCQ)
  have he := relIndex_sup_left (C.subgroupOf H) (Q.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

private theorem card_eq_index_of_disjoint_supplement (A C Q : Subgroup G)
    (hAC : A ≤ C) (hcover : C ≤ A ⊔ Q) (hd : A ⊓ Q = ⊥)
    (hn : C ≤ normalizer (Q : Set G)) : Nat.card A = Q.relIndex C := by
  have he : Q ⊔ C = Q ⊔ A := by
    apply le_antisymm
    · exact sup_le le_sup_left (hcover.trans (by rw [sup_comm]))
    · exact sup_le le_sup_left (hAC.trans le_sup_right)
  rw [←core_sup_index Q C hn,he,core_sup_index Q A (hAC.trans hn),
    ←inf_relIndex_right Q A,inf_comm Q A,hd,relIndex_bot_left]

/-- Source (11.6)(a,c) at an escaping unitary turn, using only the
three-edge path supplied by the initial core action. -/
theorem source_unitary_neighbor_core_center
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b)) :
    neighborCoreIntersection (family P) b = Z (family P) b ∧
      Nat.card (Z (family P) b) = (Q (family P) b).relIndex (Z (family P) a) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h b
  let I := neighborCoreIntersection (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hbc' : (graph (family P)).Adj (g • b) (g • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc
  let p : BasedWalk (graph (family P)) 3 b :=
    ⟨⟨a,hab.symm⟩,⟨⟨g • b,hab'⟩,⟨⟨g • c,hbc'⟩,PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨hgb,?_,trivial⟩
    intro he
    exact hac ((MulAction.injective g) ((show g • a = a from hga).trans he.symm))
  have ht := source_unitary_three_walk_transitive h hB d hc hb hcomm hbc hac Ma hm mark b
  have hz := source_unitary_remote_layer_eq_bot h hB hS d hc hb hcomm hbc hac Ma hm mark
    g hga hgb hesc
  let : IsElementaryAbelian 2 I := source_neighbor_intersection_elementary_of_remote_layer h hab hab' hz
  have hZI : Z (family P) b ≤ I :=
    source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm
  have hZbZa : Z (family P) b ≤ Z (family P) a :=
    source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
  let K := (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a) ⊓ stabilizer (family P) b
  have hIS : I ≤ (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2 :=
    (neighborCoreIntersection_le _ hab).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab')
  have hZaS : Z (family P) a ≤
      (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2 :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab')
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  have hsupp : (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2 ⊔ K =
      stabilizer (family P) (g • b) ⊓ stabilizer (family P) a :=
    source_opposite_seed_path_supplement h hB ht p hp hab'.symm
      (by change g • b ∈ [b,a,g • b,g • c]; simp)
      (by change a ∈ [b,a,g • b,g • c]; simp)
      (by change b ∈ [b,a,g • b,g • c]; simp)
  have hKZ : K ≤ normalizer (Z (family P) b : Set G) :=
    inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ b)).mp (Z_normal _ b))
  have cover (C : Subgroup G) [IsElementaryAbelian 2 C]
      (hCS : C ≤ (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2) :
      C ≤ Z (family P) b ⊔ Q (family P) (g • b) :=
    elementary_edge_cover h hB d hab'.symm (Mb.of_equiv (translated_quotient d b g))
      (Z (family P) b) C K (hZI.trans hIS) hCS inf_le_left hsupp hKZ hesc
  have hI : I = Z (family P) b := by
    apply le_antisymm ?_ hZI
    intro x hx
    have hn : Z (family P) b ≤ normalizer (Q (family P) (g • b) : Set G) :=
      (hZI.trans (neighborCoreIntersection_le _ hab)).trans (source_adjacent_core_normalizes_core h hab')
    have hm : x ∈ (Z (family P) b : Set G) * (Q (family P) (g • b) : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
      exact cover I hIS hx
    obtain ⟨z,hz',y,hy,hzy⟩ := hm
    change z*y = x at hzy
    have hyI : y ∈ I := by
      have hh := I.mul_mem (I.inv_mem (hZI hz')) hx
      rw [←hzy] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hy1 : y = 1 := mem_bot.mp (hz ▸ ⟨hyI,hy⟩)
    rw [←hzy,hy1,mul_one]
    exact hz'
  refine ⟨hI,?_⟩
  have hd : Z (family P) b ⊓ Q (family P) (g • b) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hZI).trans hz.le)
  have hn : Z (family P) a ≤ normalizer (Q (family P) (g • b) : Set G) :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_adjacent_core_normalizes_core h hab')
  have he := card_eq_index_of_disjoint_supplement _ _ _ hZbZa (cover _ hZaS) hd hn
  have hi := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (Q (family P) b) (Z (family P) a) (MulAut.conj g).injective
  rw [←Q_translate,←Z_translate,show g • a = a from hga] at hi
  exact he.trans hi

/-- The neighboring-core identity and center index from the original marking,
with the turn, escape and all path inputs discharged. -/
theorem source_unitary_neighbor_core_center_from_marking
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
 :
    neighborCoreIntersection (family P) b = Z (family P) b ∧
      Nat.card (Z (family P) b) = (Q (family P) b).relIndex (Z (family P) a) := by
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,_⟩ := source_unitary_beta_escaping_four_walk
    h hB hS d hc hb hcomm Ma hm mark
  exact source_unitary_neighbor_core_center h hB hS d hc hb hcomm hbc hac Ma hm mark
    g hga hgb hesc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
