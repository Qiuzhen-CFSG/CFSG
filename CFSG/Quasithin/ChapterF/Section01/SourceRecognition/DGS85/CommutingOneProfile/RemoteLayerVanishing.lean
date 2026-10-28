module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterPairObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedOppositeSeedOmega

/-!
# Vanishing of the remote layer on an escaping Chapter 11 turn

Let I_beta be the intersection of the neighboring alpha cores. On a
source path, assume Z_beta escapes the core at the next beta vertex.
If J = I_beta intersect Q_beta' were nonzero, separation embeds it in
the remote alpha quotient. The path fixer preserves J; together with the
edge two-core it supplies the full Sylow normalizer. Thus J has the whole
remote linear Sylow as image. This makes Z_alpha intersect Q_beta' lie
in Z_beta Z_beta'. The same path-normalizer argument at beta' makes
Z_beta cover the critical-center image. Hence the two beta centers span
Z_alpha, contradicting CenterPairObstruction.

The path supplement comes from source 6.7. No Cartan-invariance, center-size
or vanishing premise is added. The escaping orientation is explicit here;
LinearCenterEscape supplies such an orientation before choosing the source
path. ReducedRemoteLayers applies the result after general alpha selection
and transports it through the original completion inclusion.
Source: DGS85, Groups and Graphs (1985), (11.6), printed pp.172--173.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

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

private theorem elementary_linear_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (M : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (A K : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)
    (hK : K ≤ stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔ K =
      stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hKA : K ≤ normalizer (A : Set G)) (hne : ¬ A ≤ Q (family P) a) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 = A ⊔ Q (family P) a := by
  let := finite_endpoints h
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let S := E.pCoreIn 2
  let W := A ⊔ Q (family P) a
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  have hAL : A ≤ L := hAS.trans (hT ▸ map_subtype_le _)
  have hdisp : ⁅S,A⁆ ≤ Q (family P) a := by
    have hh := elementary_actor_displacement_le_kernel L (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _) M T A hAL (hT.symm ▸ hAS)
    rw [hT,QuotientGroup.ker_mk'] at hh
    exact hh.trans_eq (localGroup_core_eq (family P) d a)
  have hSW : S ≤ normalizer (W : Set G) := normalizes_join_of_displacement A _ S
    ((pCoreIn_le 2 E).trans (inf_le_left.trans (stabilizer_normalizes_Q _ a))) hdisp
  have hKW : K ≤ normalizer (W : Set G) :=
    (le_inf hKA (hK.trans (inf_le_left.trans (stabilizer_normalizes_Q _ a)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hWS : W ≤ S := sup_le hAS (Noncommuting.graph_Q_le_edgeCore h hab)
  have hs := source_linear_edge_supplement h hB d hab M e W
    ((isPGroup_pCoreIn 2 E).to_le hWS) (hWS.trans (pCoreIn_le 2 E))
    (hcover ▸ sup_le hSW hKW) (fun he => hne (le_sup_left.trans he))
  simpa only [W,sup_assoc,sup_idem] using hs

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
  have hCpre := (map_le_iff_le_comap).mp hOmega
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

open SimpleGraph SimpleGraph.PathTransitivePolygon
/-- A nonzero remote layer on an escaping source turn contradicts the
nonquadratic alpha action. All beta catalogue alternatives are retained. -/
theorem source_linear_rankOne_layer_eq_bot_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) = ⊥ := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h b
  let I := neighborCoreIntersection (family P) b
  let J := I ⊓ Q (family P) (g • b)
  let E := Z (family P) a ⊓ Q (family P) (g • b)
  have hab := source_critical_one_adjacent hc hb
  have hga' : g • a = a := hga
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [hga'] at hh
  have hbc' : (graph (family P)).Adj (g • b) (g • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc
  have hac' : a ≠ g • c := by
    intro he
    exact hac ((MulAction.injective g) (hga'.trans he))
  have hc' : IsCriticalPair (family P) a (g • b) := by
    simpa only [hga'] using criticalPair_translate (family P) hc g
  have hcomm' : ⁅Z (family P) a,Z (family P) (g • b)⁆ = ⊥ := by
    simpa only [hga',hcomm,Subgroup.map_bot] using commuting_centers_translate (family P) a b g
  have Mb' := Mb.of_equiv (translated_quotient d b g)
  have hZbZa : Z (family P) b ≤ Z (family P) a :=
    source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm
  have hJb : J ≤ Z (family P) b :=
    source_linear_rankOne_layer_le_center h hB d hc hb hbc hac Ma Mb ea g hga hgb
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_le hJb
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ Z (family P) a from inf_le_left)
  have hJE : J ≤ E := le_inf (hJb.trans hZbZa) inf_le_right
  have hcenter := source_linear_rankOne_center_intersections h hB d hc' hb hcomm' hbc' hac' Ma Mb' ea
  have hEQ : E ⊓ Q (family P) (g • c) = Z (family P) (g • b) := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hcenter.1.le
    · exact le_inf (le_inf (hcenter.1.ge.trans inf_le_left)
        ((source_Z_Q_U h (g • b)).1.trans (map_subtype_le _)))
        (hcenter.1.ge.trans inf_le_right)
  have hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
    obtain ⟨hp,hcore⟩ := source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea
    rw [sup_comm]
    exact alpha_supplement_of_pair_generation _ _ _ _ _ hp hcore
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hsep := source_rankOne_neighbor_intersection_separated h hB d hc hb hbc hac Ma Mb
    hsupp g hga hgb
  by_contra hJne
  have hJesc : ¬ J ≤ Q (family P) (g • c) := by
    intro he
    apply hJne
    exact bot_unique ((le_inf inf_le_left he).trans hsep.le)
  obtain ⟨t,htb,hta⟩ := locally_transitive (family P) hab.symm hbc
  have hta' : (g*t) • a = g • c := by rw [mul_smul,hta]
  let ec : (d.localGroup (g • c) ⧸ pCore 2 (d.localGroup (g • c))) ≃*
      (d.localGroup a ⧸ pCore 2 (d.localGroup a)) :=
    hta' ▸ translated_quotient d a (g*t)
  let K := (stabilizer (family P) (g • c) ⊓ stabilizer (family P) (g • b)) ⊓
    stabilizer (family P) b
  have hQbS : Q (family P) (g • b) ≤
      (stabilizer (family P) (g • c) ⊓ stabilizer (family P) (g • b)).pCoreIn 2 := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hbc'
  have hKJ : K ≤ normalizer (J : Set G) :=
    (le_inf (inf_le_right.trans (neighborCoreIntersection_normalized _ b))
      ((inf_le_left.trans inf_le_right).trans (stabilizer_normalizes_Q _ (g • b)))).trans
        inf_normalizer_le_normalizer_inf
  have hJfull := elementary_linear_supplement h hB d hbc'.symm (Ma.of_equiv ec)
    (ec.trans ea) J K (inf_le_right.trans hQbS) inf_le_left
    (source_opposite_seed_path_supplement h hB ht p hp hbc'.symm hgcp hgbp hbp) hKJ hJesc
  have hEcover : E ≤ J ⊔ Q (family P) (g • c) :=
    (inf_le_right.trans hQbS).trans hJfull.le
  have hEsmall : E ≤ Z (family P) b ⊔ Z (family P) (g • b) := by
    intro x hx
    have hn : J ≤ normalizer (Q (family P) (g • c) : Set G) :=
      inf_le_right.trans (source_adjacent_core_normalizes_core h hbc')
    have hm : x ∈ (J : Set G) * (Q (family P) (g • c) : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right J _ hn]
      exact hEcover hx
    obtain ⟨j,hj,y,hy,hjy⟩ := hm
    have hyE : y ∈ E := by
      have hh := E.mul_mem (E.inv_mem (hJE hj)) hx
      rw [←hjy] at hh
      simpa only [inv_mul_cancel_left] using hh
    rw [←hjy]
    exact mul_mem (mem_sup_left (hJb hj)) (mem_sup_right (hEQ ▸ ⟨hyE,hy⟩))
  let K' := (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a) ⊓ stabilizer (family P) b
  have hZaS : Z (family P) a ≤
      (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2 :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab')
  have hZaCover := elementary_edge_cover h hB d hab'.symm Mb'
    (Z (family P) b) (Z (family P) a) K' (hZbZa.trans hZaS) hZaS inf_le_left
    (source_opposite_seed_path_supplement h hB ht p hp hab'.symm hgbp ha hbp)
    (inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ b)).mp
      (Z_normal _ b))) hesc
  apply source_linear_rankOne_center_pair_ne h hB hS d hc hb hcomm hbc hac Ma Mb ea g hga hgb
  apply le_antisymm
  · intro x hx
    have hn : Z (family P) b ≤ normalizer (Q (family P) (g • b) : Set G) :=
      (hZbZa.trans (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab').trans inf_le_right)))).trans
          (stabilizer_normalizes_Q _ (g • b))
    have hm : x ∈ (Z (family P) b : Set G) * (Q (family P) (g • b) : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
      exact hZaCover hx
    obtain ⟨z,hz,y,hy,hzy⟩ := hm
    have hyZa : y ∈ Z (family P) a := by
      have hh := (Z (family P) a).mul_mem ((Z (family P) a).inv_mem (hZbZa hz)) hx
      rw [←hzy] at hh
      simpa only [inv_mul_cancel_left] using hh
    rw [←hzy]
    exact mul_mem (mem_sup_left hz) (hEsmall ⟨hyZa,hy⟩)
  · exact sup_le hZbZa (hcenter.1.ge.trans inf_le_left)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
