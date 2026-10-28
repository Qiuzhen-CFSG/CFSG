module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCenterEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicIntersections

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphExclusions

/-!
# The actual cores in the linear/dihedral Chapter 11 candidate

Every escaping two-subgroup has index two over its intersection with the
vertex core in the literal dihedral-ten quotient. Center escape and the
proved intersection-layer identity therefore give I_beta = Z_beta.
The two neighboring centers act transitively, identifying their whole
core intersection with I_beta. The opposite alpha quotient bounds the
remaining index by its field order, while the center has that full
index. Counting proves Q_alpha = Z_alpha and hence Q_beta = V_beta.

The seed, center, beta-core and edge-Sylow orders are calculated in terms
of the unchanged alpha field and |Z_beta|. The beta core has a nontrivial
central derived subgroup equal to its embedded Frattini subgroup. At
alpha field order four, the remaining input |Z_beta| = 2 supplies the
existing small nonabelian two-group obstruction, excluding the actual
local dihedral quotient. The restricted quotient comparison is proved.

These statements do not assert the missing center order, select the alpha
row or complete the other Chapter 11 profiles. The earlier local-group
inputs and both genuine quotient markings remain explicit. In particular,
the full local kernel is never identified with its two-core.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3), (11.6)--(11.7), printed pp.168--175.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private def local_quotient_at_translate {D : Type*} [Group D]
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P)) (g : G)
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    (d.localGroup (g • v) ⧸ pCore 2 (d.localGroup (g • v))) ≃* D := by
  let f := (MulEquiv.subgroupCongr (d.conjugate g v)).trans
    ((d.localGroup v).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  exact (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e

private theorem dihedral_sylow_card (T : Sylow 2 (DihedralGroup 5)) : Nat.card T = 2 := by
  rw [T.card_eq_multiplicity,DihedralGroup.nat_card]
  decide +kernel

/-- Every escaping two-subgroup at a dihedral beta vertex has index two over
its intersection with the actual vertex core. -/
theorem source_dihedral_two_subgroup_index (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAv : A ≤ stabilizer (family P) v)
    (he : ¬ A ≤ Q (family P) v) :
    (Q (family P) v).relIndex A = 2 := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  have hAL : A ≤ L := pGroup_le_localGroup (family P) d v A hp hAv
  let A₀ := A.subgroupOf L
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hker : q.ker = pCore 2 L := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 L)) x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  have hpA : IsPGroup 2 A₀ := hp.comap_subtype
  obtain ⟨T,hT⟩ := (hpA.map q).exists_le_sylow
  have hd := card_dvd_of_le hT
  rw [dihedral_sylow_card T] at hd
  have hne : Nat.card (A₀.map q) ≠ 1 := by
    intro hh
    have hk := (Subgroup.map_eq_bot_iff A₀).mp ((Subgroup.card_eq_one).mp hh)
    rw [hker] at hk
    have hm := map_mono (f := L.subtype) hk
    rw [map_subgroupOf_eq_of_le hAL] at hm
    exact he (hm.trans_eq (localGroup_core_eq (family P) d v))
  have hcard : Nat.card (A₀.map q) = 2 := by
    have hh := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd
    omega
  rw [←localGroup_core_eq (family P) d v]
  change ((pCore 2 L).map L.subtype).relIndex A = 2
  rw [←map_subgroupOf_eq_of_le hAL,relIndex_map_map_of_injective _ _ L.subtype_injective,
    ←hker,relIndex_ker]
  exact hcard

/-- The dihedral candidate's actual center seed has index two. -/
theorem source_dihedral_seed_index (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = 2 := by
  let := source_center_elementary h a
  rw [inf_relIndex_left]
  exact source_dihedral_two_subgroup_index h d b e _ (IsElementaryAbelian.isPGroup 2 _)
    ((((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ (source_critical_one_adjacent hc hb)).trans inf_le_right))
    (fun hh => hc.2 (hh.trans (source_Z_Q_U h b).2))

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- In the linear/dihedral branch the intersection of all alpha cores is
exactly the beta center, with no center-order or layer-vanishing premise. -/
theorem source_linear_dihedral_neighbor_intersection_eq_center
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b = Z (family P) b := by
  let := finite_endpoints h
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  obtain ⟨t,hta,htb,hesc⟩ := source_linear_rankOne_center_escape h hB d hc hb hcomm
    hbc hac Ma Mb ea g hga hgb
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (t • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) t).map_adj_iff.mpr hab
    change (graph (family P)).Adj (t • a) (t • b) at hh
    rwa [show t • a = a from hta] at hh
  have hZb := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    (d.localGroup b) (d.sylow_or_center b)
  have hZI : Z (family P) b ≤ neighborCoreIntersection (family P) b := by
    apply le_iInf
    intro v
    rw [hZb]
    exact (local_omega_le_neighbor_Z h d v.property).trans
      ((source_Z_Q_U h v.val).1.trans (map_subtype_le _))
  let I := neighborCoreIntersection (family P) b
  have hIa : I ≤ Q (family P) a := neighborCoreIntersection_le _ hab
  have hpI : IsPGroup 2 I := (isPGroup_pCoreIn 2 _).to_le hIa
  have hIG : I ≤ stabilizer (family P) (t • b) := hIa.trans ((source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab').trans inf_le_right))
  have eb' := local_quotient_at_translate d b t eb
  have hiI := source_dihedral_two_subgroup_index h d (t • b) eb' I hpI hIG
    (fun hh => hesc (hZI.trans hh))
  have hiZ := source_dihedral_two_subgroup_index h d (t • b) eb' (Z (family P) b)
    (hpI.to_le hZI) (hZI.trans hIG) hesc
  have he := source_linear_rankOne_layer_eq_center_inf h hB d hc hb hcomm hbc hac
    Ma Mb ea t hta htb
  have hiI' : (Z (family P) b ⊓ Q (family P) (t • b)).relIndex I = 2 := by
    rw [←he,inf_relIndex_left]
    exact hiI
  have hiZ' : (Z (family P) b ⊓ Q (family P) (t • b)).relIndex (Z (family P) b) = 2 := by
    rw [inf_relIndex_left]
    exact hiZ
  have hind := relIndex_mul_relIndex (Z (family P) b ⊓ Q (family P) (t • b))
    (Z (family P) b) I inf_le_left hZI
  rw [hiI',hiZ'] at hind
  exact le_antisymm ((relIndex_eq_one).mp (by omega : (Z (family P) b).relIndex I = 1)) hZI

private theorem core_sup_index (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : Q.relIndex (Q ⊔ C) = Q.relIndex C := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Q.le_normalizer hCQ)
  have he := relIndex_sup_left (C.subgroupOf H) (Q.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

private theorem dihedral_center_edge_supplement (h : LocallyRankOneTriple P B)
    (_hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (he : ¬ Z (family P) a ≤ Q (family P) b) :
    (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2 =
      Z (family P) a ⊔ Q (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let R := (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2
  have hZR : Z (family P) a ≤ R :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (by simpa only [R,inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab)
  have hQR : Q (family P) b ≤ R := Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hRG : R ≤ stabilizer (family P) b := (pCoreIn_le 2 _).trans inf_le_left
  have hiR := source_dihedral_two_subgroup_index h d b e R (isPGroup_pCoreIn 2 _) hRG
    (fun hh => he (hZR.trans hh))
  have hiZ := source_dihedral_two_subgroup_index h d b e (Z (family P) a)
    (IsElementaryAbelian.isPGroup 2 _) (hZR.trans hRG) he
  have hi : (Q (family P) b).relIndex (Q (family P) b ⊔ Z (family P) a) = 2 := by
    rw [core_sup_index _ _ ((hZR.trans hRG).trans (stabilizer_normalizes_Q _ b))]
    exact hiZ
  have hh := relIndex_mul_relIndex (Q (family P) b)
    (Q (family P) b ⊔ Z (family P) a) R le_sup_left (sup_le hQR hZR)
  rw [hiR,hi] at hh
  rw [sup_comm]
  exact le_antisymm ((relIndex_eq_one).mp
    (by omega : (Q (family P) b ⊔ Z (family P) a).relIndex R = 1)) (sup_le hQR hZR)

/-- The neighboring center pair acts transitively at a dihedral beta vertex. -/
theorem source_dihedral_center_pair_transitive (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    ∀ v, (graph (family P)).Adj b v →
      ∃ t ∈ Z (family P) a ⊔ Z (family P) c, t • a = v := by
  let := finite_endpoints h
  let := source_center_elementary h a
  have hab := source_critical_one_adjacent hc hb
  have hea : ¬ Z (family P) a ≤ Q (family P) b :=
    fun hh => hc.2 (hh.trans (source_Z_Q_U h b).2)
  have hec : ¬ Z (family P) c ≤ Q (family P) b := by
    obtain ⟨g,_,hz,hq,_⟩ := source_neighbor_conjugate h hab hbc
    intro hh
    apply hea
    apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp
    rwa [hz,hq]
  have hZa : Z (family P) a ≤ stabilizer (family P) b :=
    (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hgen := source_elementary_escape_edge_generation h hB d hab.symm hbc hac (.dihedral ⟨e⟩)
    (Z (family P) a) hZa (Z_le_stabilizer _ a) hea
  rw [dihedral_center_edge_supplement h hB d hbc.symm e hec,←sup_assoc] at hgen
  let W := Z (family P) a ⊔ Z (family P) c
  have hW : W ≤ stabilizer (family P) b :=
    (le_sup_left.trans hgen.le).trans (d.local_le b)
  have hn : W ≤ normalizer (Q (family P) b : Set G) :=
    hW.trans (stabilizer_normalizes_Q (family P) b)
  intro v hbv
  obtain ⟨t,ht,hta⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hbv⟩
  have ht' : t ∈ (W : Set G) * (Q (family P) b : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right W (Q (family P) b) hn,hgen]
    exact ht
  obtain ⟨w,hw,q,hq,rfl⟩ := ht'
  have hqa : q • a = a := ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)) hq
  exact ⟨w,hw,by simpa only [mul_smul,hqa] using hta⟩

/-- The intersection of the two whole alpha cores is the complete
neighboring-core intersection in the dihedral candidate. -/
theorem source_dihedral_core_pair_eq_neighbor_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    Q (family P) a ⊓ Q (family P) c = neighborCoreIntersection (family P) b :=
  source_core_pair_eq_neighbor_intersection_of_center_pair_transitive h
    (source_critical_one_adjacent hc hb) hbc
    (source_dihedral_center_pair_transitive h hB d hc hb hbc hac e)


private theorem linear_core_index {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* SL(2,k)) (T : Sylow 2 H) :
    (pCore 2 H).relIndex T = Nat.card k := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 H)) x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  rw [←hk,relIndex_ker]
  exact Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2
    (T.mapSurjective hq)).symm.toEquiv

private theorem linear_edge_core_index (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    (Q (family P) a).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = Nat.card k := by
  let := finite_endpoints h
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  rw [←hT,←localGroup_core_eq (family P) d a]
  change ((pCore 2 L).map L.subtype).relIndex ((T : Subgroup L).map L.subtype) = _
  rw [relIndex_map_map_of_injective _ _ L.subtype_injective]
  exact linear_core_index ea T

/-- The center and seed counts in the dihedral candidate retain the actual
alpha field, without assuming either center order. -/
theorem source_linear_dihedral_center_card_ratio (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) =
        Nat.card k * Nat.card (Z (family P) b) ∧
      Nat.card (Z (family P) a) = 2 * Nat.card k * Nat.card (Z (family P) b) := by
  let := finite_endpoints h
  let C := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  obtain ⟨hp,hcore⟩ := source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea
  have hsupp := alpha_supplement_of_pair_generation _ _ _ _ _ hp hcore
    ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hi := linear_edge_core_index h hB d hab ea
  rw [hsupp,core_sup_index _ C
    (inf_le_right.trans (source_adjacent_core_normalizes_core h hab.symm))] at hi
  have hic : Q (family P) a ⊓ C = Z (family P) b := by
    change Q (family P) a ⊓ (Z (family P) c ⊓ Q (family P) b) = _
    rw [←inf_assoc,(source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac
      Ma Mb ea).2.1,inf_eq_left.mpr ((source_Z_Q_U h b).1.trans (map_subtype_le _))]
  have hZC : Z (family P) b ≤ C := hic ▸ inf_le_right
  have hidx : (Z (family P) b).relIndex C = Nat.card k := by
    rw [←hic,inf_relIndex_right]
    exact hi
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) C bot_le hZC
  rw [relIndex_bot_left,relIndex_bot_left,hidx] at hcount
  obtain ⟨t,_,_,_,he⟩ := source_neighbor_conjugate h hab hbc
  have hconj : Nat.card C = Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) := by
    change Nat.card (Z (family P) c ⊓ Q (family P) b : Subgroup G) = _
    rw [←he,card_map_of_injective (MulAut.conj t).injective]
  have hseed : Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) =
      Nat.card k * Nat.card (Z (family P) b) := by
    rw [hconj] at hcount
    exact hcount.symm.trans (Nat.mul_comm _ _)
  have hcount' := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) a ⊓ Q (family P) b)
    (Z (family P) a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,source_dihedral_seed_index h d hc hb eb,hseed] at hcount'
  exact ⟨hseed,by nlinarith [hcount']⟩

private theorem linear_two_subgroup_index_le (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* SL(2,k))
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAv : A ≤ stabilizer (family P) v) :
    (Q (family P) v).relIndex A ≤ Nat.card k := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  have hAL : A ≤ L := pGroup_le_localGroup (family P) d v A hp hAv
  let A₀ := A.subgroupOf L
  have hpA : IsPGroup 2 A₀ := hp.comap_subtype
  obtain ⟨T,hT⟩ := hpA.exists_le_sylow
  have hi : (pCore 2 L).relIndex A₀ ≤ (pCore 2 L).relIndex T := by
    rw [←QuotientGroup.ker_mk' (pCore 2 L),relIndex_ker,relIndex_ker]
    exact card_le_of_le (map_mono hT)
  rw [←localGroup_core_eq (family P) d v]
  change ((pCore 2 L).map L.subtype).relIndex A ≤ Nat.card k
  rw [←map_subgroupOf_eq_of_le hAL,relIndex_map_map_of_injective _ _ L.subtype_injective]
  exact hi.trans_eq (linear_core_index e T)

/-- The dihedral candidate forces the whole alpha core to equal its
elementary center; this is a consequence, not a branch premise. -/
theorem source_linear_dihedral_core_eq_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Q (family P) a = Z (family P) a := by
  let := finite_endpoints h
  let K := Q (family P) a ⊓ Q (family P) b
  let I := neighborCoreIntersection (family P) b
  let : Finite (Q (family P) a) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hKc : K ≤ stabilizer (family P) c := inf_le_right.trans ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hbc).trans inf_le_right))
  obtain ⟨t,_,hta⟩ := locally_transitive (family P) hab.symm hbc
  have ec : (d.localGroup c ⧸ pCore 2 (d.localGroup c)) ≃* SL(2,k) :=
    hta ▸ local_quotient_at_translate d a t ea
  have hi := linear_two_subgroup_index_le h d c ec K
    ((isPGroup_pCoreIn 2 _).to_le (show K ≤ Q (family P) a from inf_le_left)) hKc
  have hKI : Q (family P) c ⊓ K = I := by
    have hp := source_dihedral_core_pair_eq_neighbor_intersection h hB d hc hb hbc hac eb
    apply le_antisymm
    · exact (le_inf (inf_le_right.trans inf_le_left) inf_le_left).trans hp.le
    · exact le_inf (neighborCoreIntersection_le _ hbc.symm)
        (le_inf (neighborCoreIntersection_le _ hab) (source_neighborCoreIntersection_le_core h hab))
  have hIK : I ≤ K := hKI ▸ inf_le_right
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) I K bot_le hIK
  rw [relIndex_bot_left,relIndex_bot_left] at hcount
  have hidx : I.relIndex K ≤ Nat.card k := by rw [←hKI,inf_relIndex_right]; exact hi
  have hKcard : Nat.card K ≤ Nat.card I * Nat.card k :=
    hcount.symm.trans_le (Nat.mul_le_mul_left _ hidx)
  have hQab : Q (family P) a ≤ stabilizer (family P) b := (source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hindex := source_dihedral_two_subgroup_index h d b eb (Q (family P) a)
    (isPGroup_pCoreIn 2 _) hQab (fun hh => hc.2
      ((((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans hh).trans (source_Z_Q_U h b).2))
  have hKindex : K.relIndex (Q (family P) a) = 2 := by
    rw [inf_relIndex_left]
    exact hindex
  have hcount' := relIndex_mul_relIndex (⊥ : Subgroup G) K (Q (family P) a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hKindex] at hcount'
  have hIZ := source_linear_dihedral_neighbor_intersection_eq_center h hB d hc hb hcomm
    hbc hac Ma ea eb g hga hgb
  have hratio := (source_linear_dihedral_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea eb).2
  change Nat.card K ≤ Nat.card (neighborCoreIntersection (family P) b) * Nat.card k at hKcard
  rw [hIZ] at hKcard
  exact (eq_of_le_of_card_ge ((source_Z_Q_U h a).1.trans (map_subtype_le _))
    (by nlinarith : Nat.card (Q (family P) a) ≤ Nat.card (Z (family P) a))).symm


/-- The actual beta core is the corrected two-seed span. Its derived and
Frattini layers coincide, are nontrivial, and lie centrally in Z_beta. -/
theorem source_linear_dihedral_beta_core_structure (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ∧
      betaSpan (stabilizer (family P) b) (Z (family P) a) = Q (family P) b ∧
      (frattini (Q (family P) b)).map (Q (family P) b).subtype = ⁅Q (family P) b,Q (family P) b⁆ ∧
      ⁅Q (family P) b,Q (family P) b⁆ ≠ ⊥ ∧
      ⁅Q (family P) b,Q (family P) b⁆ ≤ Z (family P) b ∧
      ⁅⁅Q (family P) b,Q (family P) b⁆,Q (family P) b⁆ = ⊥ := by
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  have hQa := source_linear_dihedral_core_eq_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hp := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _
    (source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea).2 hQa
  have hs := source_linear_rankOne_pair_layers h hB d hc hb hcomm hbc hac Ma Mb ea
  have hn := source_linear_rankOne_pair_nonabelian h hB d hc hb hcomm hbc hac Ma Mb ea
  dsimp only at hs
  rw [←hp] at hs hn
  exact ⟨hp,source_betaSpan_eq_core_of_pairSpan h (source_critical_one_adjacent hc hb) hbc hp.symm,
    hs.1,hn,hs.2⟩

private theorem normalized_product_card (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) :
    Nat.card A * Nat.card C = Nat.card (A ⊓ C : Subgroup G) * Nat.card (A ⊔ C : Subgroup G) := by
  have hi : A.relIndex (A ⊔ C) = (A ⊓ C).relIndex C :=
    (core_sup_index A C hn).trans (inf_relIndex_right A C).symm
  have hH := relIndex_mul_relIndex (⊥ : Subgroup G) A (A ⊔ C) bot_le le_sup_left
  have hC := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ C) C bot_le inf_le_right
  simp only [relIndex_bot_left] at hH hC
  rw [hi] at hH
  rw [←hC,←hH]
  ac_rfl

/-- The exact beta-core and edge-Sylow orders, expressed using the actual
alpha field and the still-undetermined beta-center order. -/
theorem source_linear_dihedral_core_card_ratio (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (Q (family P) b) = Nat.card k ^ 2 * Nat.card (Z (family P) b) ∧
      Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
        2 * Nat.card k ^ 2 * Nat.card (Z (family P) b) := by
  let := finite_endpoints h
  let : Finite (Z (family P) b) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  let E := Z (family P) a ⊓ Q (family P) b
  let C := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hpair := (source_linear_dihedral_beta_core_structure h hB d hc hb hcomm hbc hac
    Ma ea eb g hga hgb).1
  have hE := (source_linear_dihedral_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea eb).1
  change Nat.card E = Nat.card k * Nat.card (Z (family P) b) at hE
  obtain ⟨t,_,_,_,ht⟩ := source_neighbor_conjugate h hab hbc
  change E.map (MulAut.conj t).toMonoidHom = C at ht
  have hC : Nat.card C = Nat.card k * Nat.card (Z (family P) b) := by
    rw [←ht,card_map_of_injective (MulAut.conj t).injective,hE]
  have hn : Q (family P) b ≤ normalizer (E : Set G) :=
    (le_inf (source_adjacent_core_normalizes_center h hab) (Q (family P) b).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hprod := normalized_product_card E C (inf_le_right.trans hn)
  have hinter : E ⊓ C = Z (family P) b :=
    (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).2.2.2
  change Q (family P) b = E ⊔ C at hpair
  rw [hE,hC,hinter,←hpair] at hprod
  have hpos : 0 < Nat.card (Z (family P) b) := Nat.card_pos
  have hQ : Nat.card (Q (family P) b) = Nat.card k ^ 2 * Nat.card (Z (family P) b) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    exact hprod.symm.trans (by ring)
  have hQa := source_linear_dihedral_core_eq_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hZa := (source_linear_dihedral_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea eb).2
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Q (family P) a)
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) bot_le
    (Noncommuting.graph_Q_le_edgeCore h hab)
  rw [relIndex_bot_left,relIndex_bot_left,linear_edge_core_index h hB d hab ea,hQa,hZa] at hcount
  exact ⟨hQ,hcount.symm.trans (by ring)⟩


/-- At alpha field order four, the actual dihedral candidate is excluded
once the remaining source beta-center order is two. Core equality, both
seed orders and noncommutativity are all discharged here. -/
theorem source_linear_four_dihedral_exclusion_of_center_order (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hk : Nat.card k = 4) (hZb : Nat.card (Z (family P) b) = 2) : False := by
  let H := stabilizer (family P) b
  let L := d.localGroup b
  let R := L.subgroupOf H
  let f : R ≃* L := subgroupOfEquivOfLe (d.local_le b)
  have hQL : Q (family P) b ≤ L := (localGroup_core_eq (family P) d b) ▸ map_subtype_le _
  have hQR : pCore 2 H ≤ R := by
    intro x hx
    exact hQL (mem_map_of_mem H.subtype hx)
  have hf : ((pCore 2 H).subgroupOf R).map f.toMonoidHom = pCore 2 L := by
    apply (map_injective L.subtype_injective)
    rw [map_map]
    have he : L.subtype.comp f.toMonoidHom = H.subtype.comp R.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hQR]
    exact (localGroup_core_eq (family P) d b).symm
  let eR : (R ⧸ (pCore 2 H).subgroupOf R) ≃* DihedralGroup 5 :=
    (QuotientGroup.congr _ _ f hf).trans eb
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  have hZa : Nat.card (Z (family P) a) = 16 := by
    rw [(source_linear_dihedral_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea eb).2,hk,hZb]
  have hi : Nat.card ((Z (family P) a ⊓ Q (family P) b) ⊓
      (Z (family P) c ⊓ Q (family P) b) : Subgroup G) = 2 := by
    rw [(source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).2.2.2,hZb]
  exact source_beta_quotient_not_dihedralTen h (source_critical_one_adjacent hc hb) hbc R
    (source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea).2
    (source_linear_dihedral_core_eq_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb)
    hZa (source_dihedral_seed_index h d hc hb eb) hi
    (source_linear_rankOne_pair_nonabelian h hB d hc hb hcomm hbc hac Ma Mb ea) ⟨eR⟩


/-- The literal beta-core quotient is elementary abelian of order q_alpha²,
with its normal subgroup and quotient map unchanged. -/
theorem source_linear_dihedral_core_quotient (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    ∃ hN : ((Z (family P) b).subgroupOf (Q (family P) b)).Normal,
      letI := hN
      Nat.card (Q (family P) b ⧸ (Z (family P) b).subgroupOf (Q (family P) b)) = Nat.card k ^ 2 ∧
        IsElementaryAbelian 2 (Q (family P) b ⧸ (Z (family P) b).subgroupOf (Q (family P) b)) := by
  let := finite_endpoints h
  let : Finite (Q (family P) b) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  let : Finite (Z (family P) b) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  have hZQ : Z (family P) b ≤ Q (family P) b := (source_Z_Q_U h b).1.trans (map_subtype_le _)
  have hn : Q (family P) b ≤ normalizer (Z (family P) b : Set G) := (Q_le_stabilizer _ b).trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ b)).mp (Z_normal _ b))
  let hN : ((Z (family P) b).subgroupOf (Q (family P) b)).Normal :=
    normal_subgroupOf_of_le_normalizer hn
  let := hN
  refine ⟨hN,?_,?_⟩
  · have hratio := (source_linear_dihedral_core_card_ratio h hB d hc hb hcomm hbc hac
      Ma ea eb g hga hgb).1
    have hcount := card_eq_card_quotient_mul_card_subgroup
      ((Z (family P) b).subgroupOf (Q (family P) b))
    rw [Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv,hratio] at hcount
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Z (family P) b)) hcount.symm
  · have hs := (source_linear_dihedral_beta_core_structure h hB d hc hb hcomm hbc hac
      Ma ea eb g hga hgb).2.2
    exact @elementary_quotient_of_frattini_le (Q (family P) b) _ _ 2 _
      (isPGroup_pCoreIn 2 (stabilizer (family P) b))
      ((Z (family P) b).subgroupOf (Q (family P) b)) hN
      (map_le_iff_le_comap.mp (hs.1.trans_le hs.2.2.1))


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
