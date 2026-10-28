module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCoreGeneration

/-!
# The dihedral candidate's Chapter 11 core generation

The actual D₁₀ quotient has Sylow two-subgroups of order two. Every escaping
neighboring center therefore has the full Sylow image. Two distinct such
centers generate the local actor modulo its core and act transitively on
the star. This identifies the corrected beta span with its two seeds, and
with a linear alpha quotient proves the exact core identity (11.3)(h).

This is a step in the dihedral candidate branch, not its exclusion. The
later center orders and noncommutativity needed for that exclusion remain
separate source obligations. No center size or extraspecial structure is
assumed here, and the full local kernel is not identified with the core.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h), pp.169--171, and the candidate in (11.7), p.174.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem dihedral_center_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (he : ¬ Z (family P) a ≤ Q (family P) b) :
    (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2 =
      Z (family P) a ⊔ Q (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  have hZS : Z (family P) a ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    exact ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab)
  have hZL : Z (family P) a ≤ L := hZS.trans (map_subtype_le _)
  let A := (Z (family P) a).subgroupOf L
  let q : L →* DihedralGroup 5 := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 L := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 L)) x) = 1 ↔ _
    rw [←e.map_one,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hAT : A ≤ (T : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,hyx⟩ := hZS hx
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hne : A.map q ≠ ⊥ := by
    intro hz
    have hh := (Subgroup.map_eq_bot_iff A).mp hz
    rw [hker] at hh
    have hm := map_mono (f := L.subtype) hh
    rw [map_subgroupOf_eq_of_le hZL] at hm
    exact he (hm.trans_eq (localGroup_core_eq (family P) d b))
  have hcard : Nat.card ((T : Subgroup L).map q) = 2 := by
    change Nat.card (T.mapSurjective hq) = 2
    rw [(T.mapSurjective hq).card_eq_multiplicity,DihedralGroup.nat_card]
    decide +kernel
  have hcardA : Nat.card (A.map q) = 2 := by
    have hd := card_dvd_of_le (map_mono (f := q) hAT)
    rw [hcard] at hd
    have hne1 : Nat.card (A.map q) ≠ 1 := by
      intro hh
      exact hne ((Subgroup.card_eq_one).mp hh)
    have hh := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd
    omega
  have himage : A.map q = (T : Subgroup L).map q :=
    eq_of_le_of_card_ge (map_mono hAT) (by omega)
  have hi := congrArg (Subgroup.comap q) himage
  rw [comap_map_eq,comap_map_eq,hker,
    sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] at hi
  have hm := congrArg (Subgroup.map L.subtype) hi
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hZL,hT] at hm
  exact hm.symm.trans (congrArg (Z (family P) a ⊔ ·) (localGroup_core_eq (family P) d b))

/-- At a dihedral-ten beta vertex, the two literal Chapter 11 seeds generate the full corrected span. -/
theorem source_dihedral_betaSpan_eq_pairSpan (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    betaSpan (stabilizer (family P) b) (Z (family P) a) =
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨e⟩
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
  rw [dihedral_center_supplement h hB d hbc.symm e hec,←sup_assoc] at hgen
  let W := Z (family P) a ⊔ Z (family P) c
  have hW : W ≤ stabilizer (family P) b :=
    (le_sup_left.trans hgen.le).trans (d.local_le b)
  have hn : W ≤ normalizer (Q (family P) b : Set G) :=
    hW.trans (CommutingNontrivial.stabilizer_normalizes_Q (family P) b)
  apply source_betaSpan_eq_pairSpan_of_center_pair_transitive h hab hbc
  intro v hbv
  obtain ⟨t,ht,hta⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hbv⟩
  have ht' : t ∈ (W : Set G) * (Q (family P) b : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right W (Q (family P) b) hn,hgen]
    exact ht
  obtain ⟨w,hw,q,hq,rfl⟩ := ht'
  have hqa : q • a = a := ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)) hq
  exact ⟨w,hw,by simpa only [mul_smul,hqa] using hta⟩

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- The exact (11.3)(h) identity also holds in the linear/dihedral candidate branch. -/
theorem source_linear_dihedral_pair_core_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b) := by
  have hh := source_linear_beta_core_generation h hB d hc hb hbc hac Ma (.dihedral ⟨eb⟩) ea
  rwa [source_dihedral_betaSpan_eq_pairSpan h hB d hc hb hbc hac eb] at hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
