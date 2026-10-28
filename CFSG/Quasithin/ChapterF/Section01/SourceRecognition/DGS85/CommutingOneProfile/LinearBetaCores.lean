module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCenterEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphExclusions
public import Theory.Frattini.InvolutorySupplement

/-!
# Arbitrary linear endpoint fields in the elementary-beta core profile

For genuine SL2 markings at both endpoints, the two neighboring centers
act transitively at beta. Hence the intersection of the two alpha cores is
the intersection over all alpha neighbors. Comparing the literal quotient
images and seed orders gives Q_alpha = Z_alpha I_beta.

Since Z_alpha is central elementary in Q_alpha, their Frattini subgroups
satisfy Phi(Q_alpha) = Phi(I_beta). This subgroup is normalized at both
ends of the edge and vanishes by faithful normalizer propagation. Thus
Q_alpha is elementary. The pair-core identity now makes I_beta central
in the edge two-core, placing it in Z_beta. Consequently I_beta = Z_beta,
Q_alpha = Z_alpha, and Q_beta is the corrected Chapter 11 seed span.

The resulting derived/Frattini layers, elementary quotient Q_beta/Z_beta,
and exact order ratios retain both original fields and |Z_beta|. Neither
the field relation nor the center order is assumed. Selecting the linear
rows, proving those remaining numerical restrictions and the path profiles
are separate steps in the full source family. Only vertex stabilizers
need be finite; the ambient completion may be infinite.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3), (11.6)(a), (11.7)(e), printed pp.168--175; (3.2)(c).
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
variable {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]

private def local_quotient_at_translate {D : Type*} [Group D]
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P)) (g : G)
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    (d.localGroup (g • v) ⧸ pCore 2 (d.localGroup (g • v))) ≃* D := by
  let f := (MulEquiv.subgroupCongr (d.conjugate g v)).trans
    ((d.localGroup v).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  exact (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e

private theorem core_sup_index (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : Q.relIndex (Q ⊔ C) = Q.relIndex C := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Q.le_normalizer hCQ)
  have he := relIndex_sup_left (C.subgroupOf H) (Q.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

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

/-- Neighboring critical centers generate a transitive subgroup at every linear beta vertex. -/
theorem source_linear_center_pair_transitive (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
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
  have hgen := source_elementary_escape_edge_generation h hB d hab.symm hbc hac Mb
    (Z (family P) a) hZa (Z_le_stabilizer _ a) hea
  rw [source_linear_center_supplement h hB d hbc.symm Mb e hec,←sup_assoc] at hgen
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

/-- The two alpha cores meet in the intersection over all beta neighbors. -/
theorem source_linear_core_pair_eq_neighbor_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Q (family P) a ⊓ Q (family P) c = neighborCoreIntersection (family P) b :=
  source_core_pair_eq_neighbor_intersection_of_center_pair_transitive h
    (source_critical_one_adjacent hc hb) hbc
    (source_linear_center_pair_transitive h hB d hc hb hbc hac Mb eb)

private theorem linear_seed_index (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = Nat.card k' := by
  have hab := source_critical_one_adjacent hc hb
  have hi := linear_edge_core_index h hB d hab.symm eb
  have hs := source_linear_center_supplement h hB d hab Mb eb
    (fun hh => hc.2 (hh.trans (source_Z_Q_U h b).2))
  rw [hs,sup_comm,core_sup_index] at hi
  · rwa [inf_relIndex_left]
  · exact ((((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)).trans (stabilizer_normalizes_Q _ b)

/-- Exact seed and center ratios, retaining both arbitrary linear endpoint fields. -/
theorem source_linear_linear_center_card_ratio (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) =
        Nat.card k * Nat.card (Z (family P) b) ∧
      Nat.card (Z (family P) a) = Nat.card k' * Nat.card k * Nat.card (Z (family P) b) := by
  let := finite_endpoints h
  let C := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
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
  rw [relIndex_bot_left,relIndex_bot_left,linear_seed_index h hB d hc hb Mb eb,hseed] at hcount'
  exact ⟨hseed,by nlinarith [hcount']⟩

/-- The whole alpha core is generated by its center and the neighboring-core
intersection, for arbitrary linear fields at both endpoints. -/
theorem source_linear_linear_core_decomposition (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Q (family P) a = Z (family P) a ⊔ neighborCoreIntersection (family P) b := by
  let := finite_endpoints h
  let K := Q (family P) a ⊓ Q (family P) b
  let I := neighborCoreIntersection (family P) b
  let A := Z (family P) a
  let C := Z (family P) b
  let : Finite (Q (family P) a) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  let : Finite C := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hKc : K ≤ stabilizer (family P) c := inf_le_right.trans ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hbc).trans inf_le_right))
  obtain ⟨t,_,hta⟩ := locally_transitive (family P) hab.symm hbc
  have ec : (d.localGroup c ⧸ pCore 2 (d.localGroup c)) ≃* SL(2,k) :=
    hta ▸ local_quotient_at_translate d a t ea
  have hi := linear_two_subgroup_index_le h d c ec K
    ((isPGroup_pCoreIn 2 _).to_le (show K ≤ Q (family P) a from inf_le_left)) hKc
  have hKI : Q (family P) c ⊓ K = I := by
    have hp := source_linear_core_pair_eq_neighbor_intersection h hB d hc hb hbc hac Mb eb
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
  have hindex := linear_two_subgroup_index_le h d b eb (Q (family P) a)
    (isPGroup_pCoreIn 2 _) hQab
  have hKindex : K.relIndex (Q (family P) a) ≤ Nat.card k' := by
    rw [inf_relIndex_left]
    exact hindex
  have hcount' := relIndex_mul_relIndex (⊥ : Subgroup G) K (Q (family P) a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at hcount'
  have hQcard : Nat.card (Q (family P) a) ≤ Nat.card I * Nat.card k * Nat.card k' := by
    rw [←hcount']
    exact Nat.mul_le_mul hKcard hKindex
  have hZb := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    (d.localGroup b) (d.sylow_or_center b)
  have hCI : C ≤ I := by
    apply le_iInf
    intro v
    rw [show C = Z (family P) b from rfl,hZb]
    exact (local_omega_le_neighbor_Z h d v.property).trans
      ((source_Z_Q_U h v.val).1.trans (map_subtype_le _))
  have hCA : C ≤ A := by
    rw [show C = Z (family P) b from rfl,hZb]
    exact local_omega_le_neighbor_Z h d hab.symm
  have hAI : A ⊓ I = C := by
    apply le_antisymm
    · exact (inf_le_inf_left _ (neighborCoreIntersection_le _ hbc.symm)).trans
        (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).1.le
    · exact le_inf hCA hCI
  have hIA : I ≤ centralizer (A : Set G) :=
    (neighborCoreIntersection_le _ hab).trans (source_core_centralizes_center h a)
  have hprod := normalized_product_card A I (hIA.trans (Subgroup.centralizer_le_normalizer _))
  have hratio := (source_linear_linear_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea Mb eb).2
  change Nat.card A = Nat.card k' * Nat.card k * Nat.card C at hratio
  rw [hratio,hAI] at hprod
  have hjoin : Nat.card (A ⊔ I : Subgroup G) = Nat.card I * Nat.card k * Nat.card k' := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card C from Nat.card_pos)
    exact hprod.symm.trans (by ring)
  have hle : A ⊔ I ≤ Q (family P) a := sup_le
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)) (neighborCoreIntersection_le _ hab)
  exact (eq_of_le_of_card_ge hle (hjoin ▸ hQcard)).symm

/-- The alpha core is elementary at arbitrary linear endpoint fields.
The Frattini subgroup is normalized at both ends of the edge. -/
theorem source_linear_linear_alpha_core_elementary (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    IsElementaryAbelian 2 (Q (family P) a) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let R := Q (family P) a
  let I := neighborCoreIntersection (family P) b
  let A := Z (family P) a
  have hab := source_critical_one_adjacent hc hb
  have hIR : I ≤ R := neighborCoreIntersection_le _ hab
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  let : Finite I := Finite.of_injective (inclusion hIR) (inclusion_injective _)
  have hp : IsPGroup 2 R := isPGroup_pCoreIn 2 _
  let : Fact (IsPGroup 2 R) := ⟨hp⟩
  have hcent : I ≤ centralizer (A : Set G) := hIR.trans (source_core_centralizes_center h a)
  have hgen : I ⊔ A = R := (sup_comm I A).trans
    (source_linear_linear_core_decomposition h hB d hc hb hcomm hbc hac Ma ea Mb eb).symm
  have hphi := frattini_map_eq_of_involutory_supplement R I A hp (hp.to_le hIR)
    hgen ((le_centralizer_iff.mp hcent).trans (Subgroup.centralizer_le_normalizer _))
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx)
  rw [commutator_eq_bot_iff_le_centralizer.mpr hcent,sup_bot_eq] at hphi
  let N := (frattini R).map R.subtype
  have hna : stabilizer (family P) a ≤ normalizer (N : Set G) :=
    (stabilizer_normalizes_Q _ a).trans (normalizer_le_normalizer_characteristic_image R (frattini R))
  have hnb : stabilizer (family P) b ≤ normalizer (N : Set G) := by
    change stabilizer (family P) b ≤ normalizer ((frattini R).map R.subtype : Set G)
    rw [hphi]
    exact (neighborCoreIntersection_normalized _ b).trans
      (normalizer_le_normalizer_characteristic_image I (frattini I))
  have hN : N = ⊥ := by
    apply source_normalized_edge_eq_bot h hab N
      ((map_subtype_le _).trans (le_inf (Q_le_stabilizer _ a)
        ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right))))
    · intro v hv
      obtain ⟨t,ht,he⟩ := d.transitive a ⟨b,hab⟩ ⟨v,hv⟩
      exact ⟨t,hna (d.local_le a ht),he⟩
    · intro v hv
      obtain ⟨t,ht,he⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hv⟩
      exact ⟨t,hnb (d.local_le b ht),he⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (((frattini R).map_eq_bot_iff_of_injective R.subtype_injective).mp hN)

/-- For arbitrary linear alpha and beta, the intersection over every alpha
neighbor is precisely the original beta center. -/
theorem source_linear_linear_neighbor_intersection_eq_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    neighborCoreIntersection (family P) b = Z (family P) b := by
  let := finite_endpoints h
  let := source_linear_linear_alpha_core_elementary h hB d hc hb hcomm hbc hac Ma ea Mb eb
  let I := neighborCoreIntersection (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hIa : I ≤ Q (family P) a := neighborCoreIntersection_le _ hab
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.of_le hIa
  have hIc : I ≤ Q (family P) c := neighborCoreIntersection_le _ hbc.symm
  have hIA : I ≤ centralizer (Q (family P) a : Set G) := hIa.trans
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  obtain ⟨hp,hcore⟩ := source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea
  have hIB : I ≤ centralizer (Q (family P) b : Set G) := by
    rw [hcore]
    apply le_centralizer_iff.mpr
    apply sup_le
    · change (Z (family P) a ⊓ Q (family P) b) ⊔ (Z (family P) c ⊓ Q (family P) b) ≤ _
      exact sup_le
        (inf_le_left.trans ((le_centralizer_iff.mp (source_core_centralizes_center h a)).trans
          (centralizer_le hIa)))
        (inf_le_left.trans ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
          (centralizer_le hIc)))
    · exact inf_le_left.trans (le_centralizer_iff.mp hIA)
  apply le_antisymm
  · apply source_elementary_central_edge_le_center h hB d hab I
      (hIa.trans (Noncommuting.graph_Q_le_edgeCore h hab))
    rw [hp]
    exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hIA) (le_centralizer_iff.mp hIB))
  · have hZb := critical_end_center_of_commuting (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
      (d.localGroup b) (d.sylow_or_center b)
    apply le_iInf
    intro v
    rw [hZb]
    exact (local_omega_le_neighbor_Z h d v.property).trans
      ((source_Z_Q_U h v.val).1.trans (map_subtype_le _))

/-- Source (11.7)(e), alpha clause, without restricting either linear field. -/
theorem source_linear_linear_core_eq_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Q (family P) a = Z (family P) a := by
  rw [source_linear_linear_core_decomposition h hB d hc hb hcomm hbc hac Ma ea Mb eb,
    source_linear_linear_neighbor_intersection_eq_center h hB d hc hb hcomm hbc hac Ma ea Mb eb]
  exact sup_eq_left.mpr
    ((source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb ea).1.ge.trans inf_le_left)

/-- The actual beta core is the corrected two-seed span. Its derived and
Frattini layers coincide, are nontrivial, and lie centrally in Z_beta. -/
theorem source_linear_linear_beta_core_structure (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ∧
      betaSpan (stabilizer (family P) b) (Z (family P) a) = Q (family P) b ∧
      (frattini (Q (family P) b)).map (Q (family P) b).subtype = ⁅Q (family P) b,Q (family P) b⁆ ∧
      ⁅Q (family P) b,Q (family P) b⁆ ≠ ⊥ ∧
      ⁅Q (family P) b,Q (family P) b⁆ ≤ Z (family P) b ∧
      ⁅⁅Q (family P) b,Q (family P) b⁆,Q (family P) b⁆ = ⊥ := by
  have hQa := source_linear_linear_core_eq_center h hB d hc hb hcomm hbc hac Ma ea Mb eb
  have hp := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _
    (source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea).2 hQa
  have hs := source_linear_rankOne_pair_layers h hB d hc hb hcomm hbc hac Ma Mb ea
  have hn := source_linear_rankOne_pair_nonabelian h hB d hc hb hcomm hbc hac Ma Mb ea
  dsimp only at hs
  rw [←hp] at hs hn
  exact ⟨hp,source_betaSpan_eq_core_of_pairSpan h (source_critical_one_adjacent hc hb) hbc hp.symm,
    hs.1,hn,hs.2⟩

/-- The exact beta-core and edge-Sylow orders, expressed using the actual
alpha field and the still-undetermined beta-center order. -/
theorem source_linear_linear_core_card_ratio (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Nat.card (Q (family P) b) = Nat.card k ^ 2 * Nat.card (Z (family P) b) ∧
      Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
        Nat.card k' * Nat.card k ^ 2 * Nat.card (Z (family P) b) := by
  let := finite_endpoints h
  let : Finite (Z (family P) b) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  let E := Z (family P) a ⊓ Q (family P) b
  let C := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hpair := (source_linear_linear_beta_core_structure h hB d hc hb hcomm hbc hac
    Ma ea Mb eb).1
  have hE := (source_linear_linear_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea Mb eb).1
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
  have hQa := source_linear_linear_core_eq_center h hB d hc hb hcomm hbc hac Ma ea Mb eb
  have hZa := (source_linear_linear_center_card_ratio h hB d hc hb hcomm hbc hac Ma ea Mb eb).2
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Q (family P) a)
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) bot_le
    (Noncommuting.graph_Q_le_edgeCore h hab)
  rw [relIndex_bot_left,relIndex_bot_left,linear_edge_core_index h hB d hab ea,hQa,hZa] at hcount
  exact ⟨hQ,hcount.symm.trans (by ring)⟩


/-- The literal beta-core quotient is elementary abelian of order q_alpha²,
with its normal subgroup and quotient map unchanged. -/
theorem source_linear_linear_core_quotient (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
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
  · have hratio := (source_linear_linear_core_card_ratio h hB d hc hb hcomm hbc hac
      Ma ea Mb eb).1
    have hcount := card_eq_card_quotient_mul_card_subgroup
      ((Z (family P) b).subgroupOf (Q (family P) b))
    rw [Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv,hratio] at hcount
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Z (family P) b)) hcount.symm
  · have hs := (source_linear_linear_beta_core_structure h hB d hc hb hcomm hbc hac
      Ma ea Mb eb).2.2
    exact @elementary_quotient_of_frattini_le (Q (family P) b) _ _ 2 _
      (isPGroup_pCoreIn 2 (stabilizer (family P) b))
      ((Z (family P) b).subgroupOf (Q (family P) b)) hN
      (map_le_iff_le_comap.mp (hs.1.trans_le hs.2.2.1))


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
