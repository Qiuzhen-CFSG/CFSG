module
public import Theory.GroupTheory.Commutator.BinaryIndexTwo
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCentralLayers

/-!
# Excluding small alpha quotients in the commuting-one configuration

The opposite-seed supplement alone proves that the seed acts
nonquadratically on Z_alpha. If its displacement were fixed, the supplement
would place that displacement in Z_beta and give [Q_beta,Z_alpha] <= Z_beta.
The two adjacent centers would then generate a two-group, contradicting
their distinct fixed neighbors. This argument requires no alpha marking
and no pair-core generation hypothesis.

If the alpha edge Sylow has index two over Q_alpha, seed escape gives that
supplement and an index-two centralizing subgroup in the elementary seed.
The binary quadratic-action lemma contradicts nonquadraticity. Mapping the
actual local Sylow into a marked quotient excludes alpha D10 and alpha
SL2(2), for every beta catalogue row. Earlier local data and genuine quotient
markings remain explicit; the full local kernel is not identified with Q.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)(c), (11.3)(f), (11.5), printed pp.168--172.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem pair_two_group_of_central_displacement (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hdisp : ⁅Q (family P) b,Z (family P) a⁆ ≤ Z (family P) b)
    (hZba : Z (family P) b ≤ Z (family P) a)
    (hZbc : Z (family P) b ≤ Z (family P) c) :
    IsPGroup 2 (Z (family P) a ⊔ Z (family P) c : Subgroup G) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let M := stabilizer (family P) b
  let A := (Z (family P) a).subgroupOf M
  let C := (Z (family P) c).subgroupOf M
  let E := (Z (family P) b).subgroupOf M
  have haM : Z (family P) a ≤ M :=
    (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hcM : Z (family P) c ≤ M :=
    (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans (source_Z_Q_U h c).2).trans
      ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hcM
  have hcomm : ⁅pCore 2 M,A⁆ ≤ E := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le haM,
      map_subgroupOf_eq_of_le (Z_le_stabilizer _ b)]
    exact hdisp
  have hAE : A ≤ centralizer (E : Set M) := by
    intro x hx y hy
    apply Subtype.ext
    exact (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative (Z (family P) a))) hx y.val (hZba hy)
  have hCE : C ≤ centralizer (E : Set M) := by
    intro x hx y hy
    apply Subtype.ext
    exact (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative (Z (family P) c))) hx y.val (hZbc hy)
  have hp := isPGroup_sup_of_centralized_displacement (pCore 2 M) A C E
    (pCore_isPGroup (p := 2)) (IsElementaryAbelian.isPGroup 2 C)
    le_normalizer_of_normal le_normalizer_of_normal
    (inf_le_right.trans (source_vertex_core_selfCentralizing h b)) hcomm hAE hCE
  rw [←subgroupOf_sup haM hcM] at hp
  exact hp.of_equiv (subgroupOfEquivOfLe (sup_le haM hcM))

/-- Source (11.3)(f) from the actual opposite-seed supplement, for any
alpha row and any beta catalogue row. No pair-core identity is assumed. -/
theorem source_seed_nonquadratic_of_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a) :
    ⁅⁅Z (family P) a,Z (family P) c ⊓ Q (family P) b⁆,
      Z (family P) c ⊓ Q (family P) b⁆ ≠ ⊥ := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let C := Z (family P) c ⊓ Q (family P) b
  let E := ⁅Z (family P) a,C⁆
  have hab := source_critical_one_adjacent hc hb
  have hZa : E ≤ Z (family P) a :=
    le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans (source_adjacent_core_normalizes_center h hab))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hZa
  intro hquad
  have hEb : E ≤ Z (family P) b := by
    apply source_elementary_central_edge_le_center h hB d hab E
    · rw [hsupp]
      exact (hZa.trans ((source_Z_Q_U h a).1.trans (map_subtype_le _))).trans le_sup_right
    · rw [hsupp]
      apply le_centralizer_iff.mpr
      apply sup_le
      · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hquad)
      · exact (source_core_centralizes_center h a).trans (centralizer_le hZa)
  let R := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  have hQR : Q (family P) b ≤ R := by
    simpa only [R,inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hQdisp : ⁅Q (family P) b,Z (family P) a⁆ ≤ Z (family P) b := by
    apply (commutator_mono hQR le_rfl).trans
    rw [show R = C ⊔ Q (family P) a from hsupp]
    apply commutator_sup_le_of_relative_normal R _ _ _ (Z (family P) b)
      (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Z _ b))
      (inf_le_right.trans hQR) (Noncommuting.graph_Q_le_edgeCore h hab)
    · rw [commutator_comm]
      exact hEb
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (source_core_centralizes_center h a)).le.trans bot_le
  have hZb := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    (d.localGroup b) (d.sylow_or_center b)
  have hZba : Z (family P) b ≤ Z (family P) a := by
    rw [hZb]
    exact local_omega_le_neighbor_Z h d hab.symm
  have hZbc : Z (family P) b ≤ Z (family P) c := by
    rw [hZb]
    exact local_omega_le_neighbor_Z h d hbc
  exact source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb
    (pair_two_group_of_central_displacement h hab hbc hQdisp hZba hZbc)

private theorem supplement_of_index_two (Q C R : Subgroup G)
    (hQR : Q ≤ R) (hCR : C ≤ R) (hn : R ≤ normalizer (Q : Set G))
    (hi : Q.relIndex R = 2) (he : ¬ C ≤ Q) :
    R = C ⊔ Q ∧ Q.relIndex C = 2 := by
  let : (Q.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer hn
  have hd := relIndex_dvd_index_of_normal (Q.subgroupOf R) (C.subgroupOf R)
  rw [relIndex_subgroupOf hCR] at hd
  change Q.relIndex C ∣ Q.relIndex R at hd
  rw [hi] at hd
  have hC : Q.relIndex C = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
    (fun hh => he (relIndex_eq_one.mp hh))
  have hjoin : Q.relIndex (Q ⊔ C) = 2 := by
    have hh := relIndex_sup_left (C.subgroupOf R) (Q.subgroupOf R)
    rw [←subgroupOf_sup hQR hCR,relIndex_subgroupOf (sup_le hQR hCR),
      relIndex_subgroupOf hCR] at hh
    exact hh.trans hC
  have hm := relIndex_mul_relIndex Q (Q ⊔ C) R le_sup_left (sup_le hQR hCR)
  rw [hi,hjoin] at hm
  have hR : R ≤ Q ⊔ C := relIndex_eq_one.mp (by omega : (Q ⊔ C).relIndex R = 1)
  exact ⟨by rw [sup_comm]; exact le_antisymm hR (sup_le hQR hCR),hC⟩

/-- An index-two alpha edge quotient would force quadratic seed action,
contradicting the Chapter 11 critical configuration. -/
theorem source_alpha_edge_core_index_ne_two (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    (Q (family P) a).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ≠ 2 := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let C := Z (family P) c ⊓ Q (family P) b
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  let R := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  have hab := source_critical_one_adjacent hc hb
  have hQR : Q (family P) b ≤ R := by
    simpa only [R,inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hn := source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb
  have he : ¬ C ≤ Q (family P) a := source_seed_not_le_opposite_core h hbc.symm hab.symm
    (by intro hp; apply hn; rw [sup_comm]; exact hp)
  intro hi
  obtain ⟨hsupp,hidx⟩ := supplement_of_index_two (Q (family P) a) C R
    (Noncommuting.graph_Q_le_edgeCore h hab) (inf_le_right.trans hQR)
    (((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ a)) hi he
  exact source_seed_nonquadratic_of_supplement h hB d hc hb hcomm hbc hac Mb hsupp
    (Subgroup.quadratic_of_elementary_index_two (Z (family P) a) C (Q (family P) a)
      (inf_le_right.trans (source_adjacent_core_normalizes_center h hab))
      (source_core_centralizes_center h a) hidx)

/-- Every genuinely marked alpha quotient has Sylow two-subgroups whose
order is different from two. The edge radical and quotient map are literal. -/
theorem source_alpha_model_sylow_card_ne_two {D : Type*} [Group D]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D) (T : Sylow 2 D) :
    Nat.card T ≠ 2 := by
  let := finite_endpoints h
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let : Finite D := Finite.of_surjective e e.surjective
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨U,hU⟩ := source_edge_core_local_sylow h hB d hab
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 L)) x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  intro hcard
  apply source_alpha_edge_core_index_ne_two h hB d hc hb hcomm hbc hac Mb
  rw [←hU,←localGroup_core_eq (family P) d a]
  change ((pCore 2 L).map L.subtype).relIndex ((U : Subgroup L).map L.subtype) = _
  rw [relIndex_map_map_of_injective _ _ L.subtype_injective,←hk,relIndex_ker]
  exact (Nat.card_congr ((U.mapSurjective hq).equiv T).toEquiv).trans hcard

/-- The dihedral-ten alpha row is impossible for every beta catalogue row. -/
theorem source_alpha_dihedral_exclusion (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* DihedralGroup 5) : False := by
  let T : Sylow 2 (DihedralGroup 5) := Classical.choice inferInstance
  apply source_alpha_model_sylow_card_ne_two h hB d hc hb hcomm hbc hac Mb ea T
  rw [T.card_eq_multiplicity,DihedralGroup.nat_card]
  decide +kernel

/-- The alpha linear field cannot be the binary field; its original
field and quotient marking are retained. -/
theorem source_alpha_linear_field_card_ne_two {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    Nat.card k ≠ 2 := by
  let T : Sylow 2 SL(2,k) := Classical.choice inferInstance
  intro hcard
  apply source_alpha_model_sylow_card_ne_two h hB d hc hb hcomm hbc hac Mb ea T
  exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm.toEquiv).trans hcard

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
