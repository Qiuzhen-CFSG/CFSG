module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BetaCoreLayers
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The exact special layers of the beta core

If the full beta-core center escaped the alpha core, linear-alpha
normalizer invariance would make it supplement the alpha core in S.
Both factors centralize the first seed, contradicting the nonabelian
seed pair. Beta-star conjugacy then puts the center in every neighboring
core, whose intersection is the proved Z_beta.

The escaping remote core is disjoint from Z_beta. The path stabilizer
supplement and rank-one omega-center generation therefore make every
nontrivial beta-invariant subgroup of Z_beta equal to Z_beta. Apply this
to the nontrivial derived subgroup: the proved central Frattini bound
now gives Z(Q_beta) = Q_beta' = Phi(Q_beta) = Z_beta. Relative
self-centralization identifies Z(S) with the same subgroup.

These are literal ambient subgroup equalities, including the full center.
ReducedBetaCoreSpecial transports them through the original inclusion and
applies them to the full-Borel nonelementary branch with both U3 and SU3
markings. The exact unitary core order, natural alpha section and remaining
path/profile assembly still require their source arguments.
Source: DGS85, Groups and Graphs (1985), (11.3)(e), (11.6), and
(11.8)(f), printed pp.169--176; the path supplement is (6.7).
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
/-- The full beta-core center equals the source beta center for every beta row. -/
theorem source_beta_core_center_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    centerIn (Q (family P) b) = Z (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let C := centerIn (Q (family P) b)
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨n,hn,hi⟩ := (source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb ht p hp ha hbp hcp).2
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have hnC : stabilizer (family P) b ≤ normalizer (C : Set G) :=
    normalizes_centerIn (stabilizer_normalizes_Q (family P) b)
  have hCQ : C ≤ Q (family P) b := inf_le_left
  have hCa : C ≤ Q (family P) a := by
    by_contra he
    have hprod := source_linear_edge_supplement h hB d hab Ma (ea.trans ep.symm) C
      ((isPGroup_pCoreIn 2 _).to_le hCQ)
      (hCQ.trans (by simpa only [inf_comm] using
        ((source_Z_Q_U h b).2.trans (ballKernel_one_le_edge _ hab.symm))))
      (inf_le_right.trans hnC) he
    have hCb : C ≤ centralizer (Q (family P) b : Set G) := inf_le_right
    have hQE : Q (family P) b ≤ centralizer (E : Set G) := by
      have hQS := Noncommuting.graph_Q_le_edgeCore h hab.symm
      rw [inf_comm] at hQS
      apply hQS.trans
      rw [hprod]
      exact sup_le (hCb.trans (centralizer_le (show E ≤ Q (family P) b from inf_le_right)))
        ((source_core_centralizes_center h a).trans
          (centralizer_le (show E ≤ Z (family P) a from inf_le_left)))
    have hFE : F ≤ centralizer (E : Set G) := inf_le_right.trans hQE
    have hEE : E ≤ centralizer (E : Set G) :=
      inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (Z (family P) a))).trans (centralizer_le inf_le_left))
    have hFF : F ≤ centralizer (F : Set G) :=
      inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (Z (family P) c))).trans (centralizer_le inf_le_left))
    have hVV : E ⊔ F ≤ centralizer ((E ⊔ F : Subgroup G) : Set G) := by
      apply le_centralizer_iff.mp
      apply sup_le
      · exact le_centralizer_iff.mp (sup_le hEE hFE)
      · exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hFE) hFF)
    exact (source_seed_nonquadratic_and_pair_nonabelian_on_path h hB d hc hb hcomm
      hbc hac Ma Mb ht p hp ha hbp hcp).2 (commutator_eq_bot_iff_le_centralizer.mpr hVV)
  have hCI : C ≤ neighborCoreIntersection (family P) b := by
    apply le_iInf
    intro w
    obtain ⟨t,ht,hta⟩ := locally_transitive (family P) hab.symm w.property
    have hm := map_mono (f := (MulAut.conj t).toMonoidHom) hCa
    have heC : C.map (MulAut.conj t).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (hnC ht)
    rw [heC,←Q_translate,hta] at hm
    exact hm
  apply le_antisymm
  · exact hCI.trans_eq (source_neighbor_intersection_eq_center_on_escaping_path h hB hS d
      hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp)
  · exact le_inf ((source_Z_Q_U h b).1.trans (map_subtype_le _))
      (le_centralizer_iff.mp (source_core_centralizes_center h b))

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


/-- No proper nontrivial subgroup of Z_beta is invariant under its full stabilizer. -/
theorem source_beta_center_minimal_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (N : Subgroup G) (hNZ : N ≤ Z (family P) b) (hNne : N ≠ ⊥)
    (hnN : stabilizer (family P) b ≤ normalizer (N : Set G)) :
    N = Z (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h b
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_le hNZ
  let I := neighborCoreIntersection (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hz := source_rankOne_layer_eq_bot_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hZI : Z (family P) b ≤ I :=
    source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm
  have hNesc : ¬ N ≤ Q (family P) (g • b) := by
    intro he
    exact hNne (bot_unique ((le_inf (hNZ.trans hZI) he).trans hz.le))
  let K := (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a) ⊓ stabilizer (family P) b
  have hIS : I ≤ (stabilizer (family P) (g • b) ⊓ stabilizer (family P) a).pCoreIn 2 :=
    (neighborCoreIntersection_le _ hab).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab')
  have hcover := elementary_edge_cover h hB d hab'.symm (Mb.of_equiv (translated_quotient d b g))
    N (Z (family P) b) K (hNZ.trans (hZI.trans hIS)) (hZI.trans hIS) inf_le_left
    (source_opposite_seed_path_supplement h hB ht p hp hab'.symm hgbp ha hbp)
    (inf_le_right.trans hnN) hNesc
  apply le_antisymm hNZ
  intro x hx
  have hn : N ≤ normalizer (Q (family P) (g • b) : Set G) :=
    (hNZ.trans (hZI.trans (neighborCoreIntersection_le _ hab))).trans
      (source_adjacent_core_normalizes_core h hab')
  have hm : x ∈ (N : Set G) * (Q (family P) (g • b) : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
    exact hcover hx
  obtain ⟨z,hz',y,hy,hzy⟩ := hm
  change z*y = x at hzy
  have hyI : y ∈ I := by
    have hh := I.mul_mem (I.inv_mem (hZI (hNZ hz'))) (hZI hx)
    rw [←hzy] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hy1 : y = 1 := mem_bot.mp (hz ▸ ⟨hyI,hy⟩)
  rw [←hzy,hy1,mul_one]
  exact hz'

/-- The full center, derived group and Frattini subgroup are exactly the same
nontrivial elementary subgroup Z_beta. This supplies the special-group
equalities of (11.8)(f) without assuming the core order. -/
theorem source_beta_core_special_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    centerIn (Q (family P) b) = Z (family P) b ∧
      ⁅Q (family P) b,Q (family P) b⁆ = Z (family P) b ∧
      (frattini (Q (family P) b)).map (Q (family P) b).subtype = Z (family P) b ∧
      Z (family P) b ≠ ⊥ := by
  let := finite_endpoints h
  let R := Q (family P) b
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  let : Fact (IsPGroup 2 R) := ⟨isPGroup_pCoreIn 2 _⟩
  obtain ⟨hphi,hder,hcl,hpow,hnon,_⟩ := source_beta_core_layers_on_escaping_path h hB hS d
    hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hnD : stabilizer (family P) b ≤ normalizer ((⁅R,R⁆ : Subgroup G) : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp ((stabilizer_normalizes_Q _ b) hx)]
  have heD := source_beta_center_minimal_on_escaping_path h hB hS d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp ⁅R,R⁆ hder hnon hnD
  have hDP : ⁅R,R⁆ ≤ (frattini R).map R.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  refine ⟨source_beta_core_center_on_escaping_path h hB hS d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp,heD,?_,?_⟩
  · exact le_antisymm hphi (heD ▸ hDP)
  · exact heD ▸ hnon

/-- The entire edge two-core has the same center as its beta core. -/
theorem source_edge_core_center_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    centerIn ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
      Z (family P) b := by
  let := finite_endpoints h
  let S := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  have hab := source_critical_one_adjacent hc hb
  have hQbS : Q (family P) b ≤ S := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hcent := source_beta_core_center_on_escaping_path h hB hS d hc hb hcomm hbc hac Ma Mb
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  apply le_antisymm
  · apply le_trans ?_ hcent.le
    have hC : centerIn S ≤ centralizer (Q (family P) b : Set G) :=
      inf_le_right.trans (centralizer_le hQbS)
    exact le_inf ((le_inf (inf_le_left.trans ((pCoreIn_le 2 _).trans inf_le_right)) hC).trans
      (source_core_selfCentralizing_in_vertex h b)) hC
  · apply le_inf (((source_Z_Q_U h b).1.trans (map_subtype_le _)).trans hQbS)
    obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
    have hSL : S ≤ d.localGroup b := by
      have hh := map_subtype_le (T : Subgroup (d.localGroup b))
      rw [hT,inf_comm] at hh
      exact hh
    have hz := critical_end_center_of_commuting (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
      (d.localGroup b) (d.sylow_or_center b)
    intro x hx
    rw [hz] at hx
    exact centralizer_le hSL ((mem_omegaCenterIn_iff _ _).mp hx).2.1


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
