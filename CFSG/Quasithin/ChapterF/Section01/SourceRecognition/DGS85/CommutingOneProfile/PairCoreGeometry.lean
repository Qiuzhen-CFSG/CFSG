module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneCenterIntersections

/-!
# The general Chapter 11 pair-core geometry

Write L = <Z_alpha,Z_gamma>, D = Q_alpha intersect Q_gamma, and
V = <Z_alpha intersect Q_beta,Z_gamma intersect Q_beta>. Distinct
neighboring Sylows have intersection in the intrinsic beta core: a
nontrivial quotient intersection would contain a common involution and
force the two Sylows to agree. Thus D lies in Q_beta. The mixed-center
identities then give D intersect V = Z_alpha intersect Z_gamma.

Both D and V are normal in L Q_beta, D centralizes L, and [Q_beta,L]
lies in V. The elementary Sylow-center calculation at both alpha vertices
also gives [Q_beta,V] <= D, without selecting a linear alpha row. The
critical centralizer alternative identifies D exactly with C_Q_beta(L).

These are the geometric and action inputs for the literal quotient used
in (11.3). The general core-generation identity (11.3)(h), edge-core
product (11.4), alpha selection and the remaining profiles are separate.
The full local kernels are never identified with the two-cores.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)--(11.3), printed pp.168--171; (5.1), (5.9), (6.2).
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem local_sylow_inf_le_core {L : Type*} [Group L] [Finite L]
    (M : IsRankOneModel (L ⧸ pCore 2 L)) (S T : Sylow 2 L) (hne : S ≠ T) :
    (S : Subgroup L) ⊓ T ≤ pCore 2 L := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let A := ((S : Subgroup L) ⊓ T).map q
  have hp : IsPGroup 2 A := (S.isPGroup'.to_le inf_le_left).map q
  have hA : A = ⊥ := by
    by_contra hn
    have hcard : Nat.card A ≠ 1 := fun he => hn (Subgroup.card_eq_one.mp he)
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 2 (hp.card_eq_or_dvd.resolve_left hcard)
    have hx1 : (x : L ⧸ pCore 2 L) ≠ 1 := by
      intro he
      have hh : x = 1 := Subtype.ext he
      rw [hh,orderOf_one] at hx
      omega
    have hx2 : (x : L ⧸ pCore 2 L)^2 = 1 :=
      congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
    have heq := source_rank_one_sylow_eq_of_common_involution M
      (pCore_quotient_pCore_eq_bot 2) S' T' x
      ((map_mono inf_le_left) x.property) ((map_mono inf_le_right) x.property) hx1 hx2
    apply hne
    apply Sylow.ext
    have hh := congrArg (fun R : Sylow 2 (L ⧸ pCore 2 L) => (R : Subgroup _).comap q) heq
    change ((S : Subgroup L).map q).comap q = ((T : Subgroup L).map q).comap q at hh
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal S),
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] using hh
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hA

/-- A two-subgroup fixing two different neighbors lies in the actual vertex core. -/
theorem source_two_neighbor_two_group_le_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (A : Subgroup G) (hp : IsPGroup 2 A)
    (hAa : A ≤ stabilizer (family P) a) (hAb : A ≤ stabilizer (family P) b)
    (hAc : A ≤ stabilizer (family P) c) : A ≤ Q (family P) b := by
  let := finite_endpoints h
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  have hAL : A ≤ L := pGroup_le_localGroup (family P) d b A hp hAb
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hab.symm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hbc
  have hRT : R ≠ T := by
    intro he
    apply hac
    symm
    apply source_edge_sylow_unique_neighbor h d hab.symm hbc Mb R hR
    rw [he,hT]
    exact (pCoreIn_le 2 _).trans inf_le_right
  have hAedge {w : Vertex (family P)} (hbw : (graph (family P)).Adj b w)
      (hAw : A ≤ stabilizer (family P) w) :
      A ≤ (stabilizer (family P) b ⊓ stabilizer (family P) w).pCoreIn 2 := by
    let E := stabilizer (family P) b ⊓ stabilizer (family P) w
    let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) b from inf_le_left))
      (inclusion_injective _)
    exact pGroup_le_core_of_core_sylow E A (le_inf hAb hAw) hp (source_edge_core_sylow h hB hbw)
  have hAR : A.subgroupOf L ≤ (R : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := (hR ▸ hAedge hab.symm hAa) hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hAT : A.subgroupOf L ≤ (T : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := (hT ▸ hAedge hbc hAc) hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hh := map_mono (f := L.subtype) ((le_inf hAR hAT).trans (local_sylow_inf_le_core Mb R T hRT))
  rw [map_subgroupOf_eq_of_le hAL] at hh
  exact hh.trans_eq (localGroup_core_eq (family P) d b)

/-- The source D = Q_alpha intersect Q_alpha+2 lies in Q_beta, with no alpha marking. -/
theorem source_rankOne_pair_core_le_beta (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    Q (family P) a ⊓ Q (family P) c ≤ Q (family P) b := by
  apply source_two_neighbor_two_group_le_core h hB d hab hbc hac Mb _
    ((isPGroup_pCoreIn 2 (stabilizer (family P) a)).to_le inf_le_left)
    (inf_le_left.trans (Q_le_stabilizer _ a)) _ (inf_le_right.trans (Q_le_stabilizer _ c))
  exact inf_le_left.trans ((source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab).trans inf_le_right))

/-- DGS (11.3)(a): the actual two-core pair intersects the two-seed group in
exactly the intersection of the whole centers, before alpha selection. -/
theorem source_rankOne_pair_core_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    (Q (family P) a ⊓ Q (family P) c) ⊓
        pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) =
      Z (family P) a ⊓ Z (family P) c := by
  have hab := source_critical_one_adjacent hc hb
  have hJQ := (inf_le_inf ((source_Z_Q_U h a).1.trans (map_subtype_le _))
    ((source_Z_Q_U h c).1.trans (map_subtype_le _))).trans
      (source_rankOne_pair_core_le_beta h hB d hab hbc hac Mb)
  have hm := source_rankOne_mixed_center_intersections h hB d hc hb hbc Mb
  have hn : (Z (family P) c ⊓ Q (family P) b : Subgroup G) ≤
      normalizer ((Z (family P) a ⊓ Q (family P) b : Subgroup G) : Set G) :=
    inf_le_right.trans ((le_inf (source_adjacent_core_normalizes_center h hab)
      (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ((Z (family P) a ⊓ Q (family P) b : Subgroup G) : Set G) *
        ((Z (family P) c ⊓ Q (family P) b : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
      exact hx.2
    obtain ⟨e,he,f,hf,rfl⟩ := hx'
    have hfQa : f ∈ Q (family P) a := by
      have hh := (Q (family P) a).mul_mem
        ((Q (family P) a).inv_mem (((source_Z_Q_U h a).1.trans (map_subtype_le _)) he.1)) hx.1.1
      simpa only [inv_mul_cancel_left] using hh
    have hfJ := hm.2.le ⟨hfQa,hf.1⟩
    have heQc : e ∈ Q (family P) c := by
      have hh := (Q (family P) c).mul_mem hx.1.2
        ((Q (family P) c).inv_mem (((source_Z_Q_U h c).1.trans (map_subtype_le _)) hf.1))
      simpa only [mul_inv_cancel_right] using hh
    exact (Z (family P) a ⊓ Z (family P) c).mul_mem (hm.1.le ⟨he.1,heQc⟩) hfJ
  · exact le_inf (inf_le_inf ((source_Z_Q_U h a).1.trans (map_subtype_le _))
      ((source_Z_Q_U h c).1.trans (map_subtype_le _)))
      ((le_inf inf_le_left hJQ).trans le_sup_left)

/-- Both literal source factors are normal under L Q_beta; D centralizes L.
Normality is only asserted in that subgroup. -/
theorem source_pair_core_normalizers (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) :
    let L := Z (family P) a ⊔ Z (family P) c
    let D := Q (family P) a ⊓ Q (family P) c
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    L ≤ centralizer (D : Set G) ∧
      L ⊔ Q (family P) b ≤ normalizer (D : Set G) ∧
      L ⊔ Q (family P) b ≤ normalizer (V : Set G) ∧
      ⁅Q (family P) b,L⁆ ≤ V := by
  let L := Z (family P) a ⊔ Z (family P) c
  let D := Q (family P) a ⊓ Q (family P) c
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  have hLD : L ≤ centralizer (D : Set G) := sup_le
    ((le_centralizer_iff.mp (source_core_centralizes_center h a)).trans (centralizer_le inf_le_left))
    ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans (centralizer_le inf_le_right))
  have hQD : Q (family P) b ≤ normalizer (D : Set G) :=
    (le_inf (source_adjacent_core_normalizes_core h hab.symm)
      (source_adjacent_core_normalizes_core h hbc)).trans inf_normalizer_le_normalizer_inf
  have hQV : Q (family P) b ≤ normalizer (V : Set G) := by
    apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (le_inf (source_adjacent_core_normalizes_center h hab)
        (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf
    · exact (le_inf (source_adjacent_core_normalizes_center h hbc.symm)
        (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hLV : L ≤ normalizer (V : Set G) := source_center_pair_normalizes_pairSpan h hab hbc
  refine ⟨hLD,sup_le (hLD.trans (Subgroup.centralizer_le_normalizer _)) hQD,
    sup_le hLV hQV,?_⟩
  rw [commutator_comm]
  apply commutator_sup_le_of_relative_normal L _ _ _ V hLV le_sup_left le_sup_right
  · exact (le_inf
      (le_normalizer_iff_commutator_le_left.mp (source_adjacent_core_normalizes_center h hab))
      (le_normalizer_iff_commutator_le_right.mp
        (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
          (source_adjacent_core_normalizes_core h hab)))).trans le_sup_left
  · exact (le_inf
      (le_normalizer_iff_commutator_le_left.mp (source_adjacent_core_normalizes_center h hbc.symm))
      (le_normalizer_iff_commutator_le_right.mp
        (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
          (source_adjacent_core_normalizes_core h hbc.symm)))).trans le_sup_right

private theorem edge_elementary_displacement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAQ : A ≤ Q (family P) b) :
    ⁅Q (family P) b,A⁆ ≤ Q (family P) a := by
  let := finite_endpoints h
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  have hQT : Q (family P) b ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hAT := hAQ.trans hQT
  have hh := elementary_actor_displacement_le_kernel L (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) Ma T A (hAT.trans (map_subtype_le _)) hAT
  rw [QuotientGroup.ker_mk'] at hh
  exact ((commutator_mono hQT le_rfl).trans hh).trans_eq (localGroup_core_eq (family P) d a)

/-- The beta core acts trivially on the literal two-seed quotient V/(D intersect V).
Every alpha catalogue row is allowed; the other alpha marking is transported
through the same center-pair conjugator. -/
theorem source_rankOne_pair_core_action (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    ⁅Q (family P) b,pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)⁆ ≤
      Q (family P) a ⊓ Q (family P) c := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  let D := Q (family P) a ⊓ Q (family P) c
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves h hB d hc hb hbc Mb
  have heL : (d.localGroup a).map (MulAut.conj g).toMonoidHom = d.localGroup c := by
    rw [←d.conjugate,hga]
  let eL := ((d.localGroup a).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr heL)
  let eq := QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  have Mc := Ma.of_equiv eq.symm
  have hEF : ⁅Q (family P) b,E⁆ ≤ D := by
    apply le_inf _ (edge_elementary_displacement h hB d hbc.symm Mc E inf_le_right)
    exact (commutator_mono le_rfl inf_le_left).trans
      ((le_normalizer_iff_commutator_le_right.mp (source_adjacent_core_normalizes_center h hab)).trans
        ((source_Z_Q_U h a).1.trans (map_subtype_le _)))
  have hFE : ⁅Q (family P) b,F⁆ ≤ D := by
    apply le_inf (edge_elementary_displacement h hB d hab Ma F inf_le_right)
    exact (commutator_mono le_rfl inf_le_left).trans
      ((le_normalizer_iff_commutator_le_right.mp (source_adjacent_core_normalizes_center h hbc.symm)).trans
        ((source_Z_Q_U h c).1.trans (map_subtype_le _)))
  have hnD : Q (family P) b ≤ normalizer (D : Set G) :=
    le_sup_right.trans (source_pair_core_normalizers h hab hbc).2.1
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (Q (family P) b) E F _ D hnD
    inf_le_right inf_le_right ((commutator_comm E _).trans_le hEF)
      ((commutator_comm F _).trans_le hFE)

private theorem critical_two_actor_kernel (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAa : A ≤ stabilizer (family P) a) :
    A ⊓ centralizer (Z (family P) a : Set G) = A ⊓ Q (family P) a := by
  let := finite_endpoints h
  have hSyl : ∃ T : Sylow 2 (stabilizer (family P) a ⊓ centralizer (Z (family P) a : Set G) : Subgroup G),
      (T : Subgroup (stabilizer (family P) a ⊓ centralizer (Z (family P) a : Set G) : Subgroup G)).map
        (stabilizer (family P) a ⊓ centralizer (Z (family P) a : Set G)).subtype = Q (family P) a := by
    rcases d.sylow_or_center a with hs | he
    · exact hs
    · obtain ⟨T,T',hTT⟩ := d.common_sylow a b (source_critical_one_adjacent hc hb)
      exact (critical_start_not_central (family P) (fun v => (source_Z_Q_U h v).1) hc
        (by simpa only [SimpleGraph.dist_self,hb] using (by decide : (0:ℕ)<1))
        (d.localGroup a) T T' hTT (d.sylow_le a T) he.le).elim
  exact Noncommuting.inf_centralizer_eq_inf_core (stabilizer (family P) a)
    (Q (family P) a) (Z (family P) a) A hp hAa (Q_le_stabilizer _ _)
    (source_core_centralizes_center h a) (stabilizer_normalizes_Q _ a) hSyl

/-- The source D is exactly the centralizer of the two centers inside Q_beta.
This identifies the kernel before any model selection for alpha. -/
theorem source_rankOne_pair_core_centralizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    Q (family P) b ⊓ centralizer ((Z (family P) a ⊔ Z (family P) c : Subgroup G) : Set G) =
      Q (family P) a ⊓ Q (family P) c := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hg,hga⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨c,hbc⟩
  have hgb : g • b = b := d.local_le b hg
  have hcc : IsCriticalPair (family P) c b := by
    simpa only [hga,hgb] using criticalPair_translate (family P) hc g
  have hQa : Q (family P) b ≤ stabilizer (family P) a :=
    (source_Z_Q_U h b).2.trans ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)
  have hQc : Q (family P) b ≤ stabilizer (family P) c :=
    (source_Z_Q_U h b).2.trans ((ballKernel_one_le_edge _ hbc).trans inf_le_right)
  have hka := critical_two_actor_kernel h d hc hb (Q (family P) b) (isPGroup_pCoreIn 2 _) hQa
  have hkc := critical_two_actor_kernel h d hcc hb (Q (family P) b) (isPGroup_pCoreIn 2 _) hQc
  apply le_antisymm
  · intro x hx
    exact ⟨(hka.le ⟨hx.1,centralizer_le (show Z (family P) a ≤ Z (family P) a ⊔ Z (family P) c from le_sup_left) hx.2⟩).2,
      (hkc.le ⟨hx.1,centralizer_le (show Z (family P) c ≤ Z (family P) a ⊔ Z (family P) c from le_sup_right) hx.2⟩).2⟩
  · exact le_inf (source_rankOne_pair_core_le_beta h hB d hab hbc hac Mb)
      (le_centralizer_iff.mp (source_pair_core_normalizers h hab hbc).1)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
