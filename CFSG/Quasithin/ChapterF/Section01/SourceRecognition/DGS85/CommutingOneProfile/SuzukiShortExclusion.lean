module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearEscapingShortWalks
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SuzukiExclusion

/-!
# The Suzuki contradiction from the short commuting-one source path

The actual linear alpha marking and three-walk transitivity construct an
escaping turn whose remote layer is trivial. The same three-edge walk
supplies the opposite edge supplement. The rank-one omega calculation
then identifies the whole neighboring-core intersection with the beta
center. In the Suzuki row the two alpha cores give exactly this intersection,
so the adjacent-core intersection lies in the alpha center. The full
edge-core product and the Frattini argument make the beta quotient
of the edge core elementary, contradicting every Suzuki Sylow, including
Sz(2).

This is the algebraic compatibility exclusion consumed by the marked-five
A5--Sz(2) branch. It requires no four-walk or final marked-amalgam recognition.
The exact full core product and three-walk action are explicit inputs supplied
by the preceding source proofs. Source: DGS85, Groups and Graphs (1985),
(11.6) and the Suzuki contradiction in (11.8), printed pp.173--176.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
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

private theorem source_neighbor_center_of_remote_layer_and_three_walks
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    (hz : neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) = ⊥)
    (ht : ∀ v, RootPathTransitive (graph (family P)) G v 3) :
    neighborCoreIntersection (family P) b = Z (family P) b := by
  let := finite_endpoints h
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
  let : IsElementaryAbelian 2 I := source_neighbor_intersection_elementary_of_remote_layer h hab hab' hz
  have hZI : Z (family P) b ≤ I :=
    source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm
  let K := (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a) ⊓ stabilizer (family P) b
  have hIS : I ≤ (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2 :=
    (neighborCoreIntersection_le _ hab).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab')
  have hsupp : (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2 ⊔ K =
      stabilizer (family P) (g • b) ⊓ stabilizer (family P) a :=
    source_opposite_seed_path_supplement h hB (ht b) p hp hab'.symm
      (by change g • b ∈ [b,a,g • b,g • c]; simp)
      (by change a ∈ [b,a,g • b,g • c]; simp)
      (by change b ∈ [b,a,g • b,g • c]; simp)
  have hcover := elementary_edge_cover h hB d hab'.symm (Mb.of_equiv (translated_quotient d b g))
    (Z (family P) b) I K (hZI.trans hIS) hIS inf_le_left hsupp
    (inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ b)).mp
      (Z_normal _ b))) hesc
  apply le_antisymm ?_ hZI
  intro x hx
  have hn : Z (family P) b ≤ normalizer (Q (family P) (g • b) : Set G) :=
    (hZI.trans (neighborCoreIntersection_le _ hab)).trans (source_adjacent_core_normalizes_core h hab')
  have hm : x ∈ (Z (family P) b : Set G) * (Q (family P) (g • b) : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
    exact hcover hx
  obtain ⟨z,hz',y,hy,hzy⟩ := hm
  change z*y = x at hzy
  have hyI : y ∈ I := by
    have hh := I.mul_mem (I.inv_mem (hZI hz')) hx
    rw [←hzy] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hy1 : y = 1 := mem_bot.mp (hz ▸ ⟨hyI,hy⟩)
  rw [←hzy,hy1,mul_one]
  exact hz'

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- Every marked Suzuki beta, including Sz(2), is excluded using the actual
linear alpha, full edge-core product, and three-walk action. All turn,
escape, remote-layer and path-supplement premises are discharged. -/
theorem source_linear_suzuki_exclusion_of_three_walks
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m)
    (hprod : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b)
    (ht : ∀ v, RootPathTransitive (graph (family P)) G v 3) : False := by
  let Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .suzuki m ⟨eb⟩
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,hzero⟩ :=
    source_linear_escaping_remote_layer_of_three_walks h hB hS d hc hb hcomm Ma Mb ea ht
  have hcenter := source_neighbor_center_of_remote_layer_and_three_walks
    h hB hS d hc hb hcomm hbc hac Mb g hga hgb hesc hzero ht
  have hD := (source_suzuki_core_pair_eq_neighbor_intersection h hB d hc hb hbc hac m eb).trans hcenter
  have hab := source_critical_one_adjacent hc hb
  have hZE : Z (family P) b ≤ Z (family P) a ⊓ Q (family P) b := le_inf
    (source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm)
    ((source_Z_Q_U h b).1.trans (map_subtype_le _))
  have hI := source_pair_adjacent_core_intersection h hB d hc hb hbc hac Mb
  rw [hD,sup_eq_left.mpr hZE] at hI
  have he := source_beta_quotient_elementary_of_core_intersection h hab _ hprod (hI.le.trans inf_le_left)
  have helem : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2
        (((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2) ⧸
          (Q (family P) b).subgroupOf ((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2)) := by
    rw [inf_comm (stabilizer (family P) b) (stabilizer (family P) a)]
    exact ⟨_,he⟩
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    Finite.of_equiv (SuzukiMatrixGroup m) eb.symm.toEquiv
  obtain ⟨hN,he⟩ := helem
  let := hN
  let := he
  obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow h hB d hab.symm
  let : IsElementaryAbelian 2 T := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let U := T.mapSurjective (f := eb.toMonoidHom) eb.surjective
  let : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.map (A := (T : Subgroup (d.localGroup b ⧸ pCore 2 (d.localGroup b)))) eb.toMonoidHom
  have hω : omegaCenterIn (U : Subgroup (SuzukiMatrixGroup m)) = U := by
    apply le_antisymm (map_subtype_le _)
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hx,
      fun y hy => congrArg Subtype.val (mul_comm (⟨y,hy⟩ : U) (⟨x,hx⟩ : U)),
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have hi := (suzukiSylow_omegaCenter_card_index m U).2
  rw [hω,relIndex_self] at hi
  have hp := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : 2*m+1 ≠ 0)
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
