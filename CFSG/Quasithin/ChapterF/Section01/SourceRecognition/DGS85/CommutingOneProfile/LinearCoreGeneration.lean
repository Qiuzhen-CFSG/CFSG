module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneSeeds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicGeneration
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage

/-!
# Linear quotient branches of the Chapter 11 core identities

Normalizer invariance in a binary SL₂ quotient makes every escaping normal
part of an edge Sylow have the full Sylow image. Applied to the corrected
beta span, this proves the edge-core product (11.4) whenever the actual
alpha quotient is linear, for every beta rank-one row. Intersecting the
supplement with Q_beta gives generation by that full corrected span.

When beta is also linear, the two neighboring centers generate its local
actor modulo its core and hence act transitively on its star. Their two
seeds therefore generate the corrected beta span. This proves the exact
pair-core identity (11.3)(h) in this branch at all binary field sizes.

The actual quotient isomorphisms and earlier local-group inputs are explicit.
These are branch results: selection of the linear alpha row, the non-linear
beta pair-core identity, and the remaining (11.7)--(11.8) profiles are not
asserted. The full local kernels remain distinct from the two-cores.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.5), printed pp.169--172, and the rank-one facts (5.1)--(5.2).
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- Normalizer invariance and escape in the literal linear quotient give the edge Sylow. -/
theorem source_linear_edge_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (M : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (V : Subgroup G) (hp : IsPGroup 2 V)
    (hVE : V ≤ stabilizer (family P) a ⊓ stabilizer (family P) b)
    (hnV : stabilizer (family P) a ⊓ stabilizer (family P) b ≤ normalizer (V : Set G))
    (heV : ¬ V ≤ Q (family P) a) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 = V ⊔ Q (family P) a := by
  let := finite_endpoints h
  let L := d.localGroup a
  let E := stabilizer (family P) a ⊓ stabilizer (family P) b
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) a from inf_le_left))
    (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  have hVS : V ≤ E.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow E V hVE hp (source_edge_core_sylow h hB hab)
  have hVL : V ≤ L := hVS.trans (hT ▸ map_subtype_le _)
  let V₀ := V.subgroupOf L
  let q : L →* SL(2,k) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 L := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 L)) x) = 1 ↔ _
    rw [←e.map_one,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hVT : V₀ ≤ (T : Subgroup L) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := (hT ▸ hVS) hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hn : normalizer (T : Set L) ≤ normalizer (V₀ : Set L) := by
    rw [←(source_edge_local_normalizer h d hab M T hT).2]
    intro x hx
    exact le_normalizer_comap L.subtype (hnV ⟨d.local_le a x.property,hx⟩)
  have he : ¬ V₀ ≤ q.ker := by
    rw [hker]
    intro hh
    apply heV
    have hm := map_mono (f := L.subtype) hh
    rw [map_subgroupOf_eq_of_le hVL] at hm
    exact hm.trans_eq (localGroup_core_eq (family P) d a)
  have hi := congrArg (Subgroup.comap q)
    (Matrix.SpecialLinearGroup.normalizer_invariant_image_eq_sylow T q hq V₀ hVT he hn)
  rw [comap_map_eq,comap_map_eq,hker,
    sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] at hi
  have hm := congrArg (Subgroup.map L.subtype) hi
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVL,hT] at hm
  exact hm.symm.trans (congrArg (V ⊔ ·) (localGroup_core_eq (family P) d a))


/-- The full corrected beta span supplements the alpha core in the edge Sylow. -/
theorem source_linear_betaSpan_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      betaSpan (stabilizer (family P) b) (Z (family P) a) ⊔ Q (family P) a := by
  have hab := source_critical_one_adjacent hc hb
  let V := betaSpan (stabilizer (family P) b) (Z (family P) a)
  have hVQ : V ≤ Q (family P) b := betaSpan_le_core _ _
  apply source_linear_edge_supplement h hB d hab Ma e V (betaSpan_isPGroup _ _)
  · exact hVQ.trans (by simpa only [inf_comm] using
      ((source_Z_Q_U h b).2.trans (ballKernel_one_le_edge _ hab.symm)))
  · exact inf_le_right.trans (le_normalizer_conjugateSpanBy _ _)
  · have hn := source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb
    have he := source_seed_not_le_opposite_core h hbc.symm hab.symm
      (by intro hp; apply hn; rw [sup_comm]; exact hp)
    intro hh
    exact he ((le_sup_right.trans (source_pairSpan_le_betaSpan h hab hbc)).trans hh)

/-- The edge-two-core product, with no restriction on the beta model. -/
theorem source_linear_edge_core_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b := by
  have hab := source_critical_one_adjacent hc hb
  apply le_antisymm
  · rw [source_linear_betaSpan_supplement h hB d hc hb hbc hac Ma Mb e]
    exact sup_le ((betaSpan_le_core _ _).trans le_sup_right) le_sup_left
  · exact sup_le (Noncommuting.graph_Q_le_edgeCore h hab)
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm)

/-- Intersecting the edge supplement with Q_beta gives generation by its full corrected span. -/
theorem source_linear_beta_core_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    Q (family P) b = betaSpan (stabilizer (family P) b) (Z (family P) a) ⊔
      (Q (family P) a ⊓ Q (family P) b) := by
  have hab := source_critical_one_adjacent hc hb
  let V := betaSpan (stabilizer (family P) b) (Z (family P) a)
  have hVQ : V ≤ Q (family P) b := betaSpan_le_core _ _
  have hgen := source_linear_betaSpan_supplement h hB d hc hb hbc hac Ma Mb e
  have hQsub : Q (family P) b ≤ V ⊔ Q (family P) a := by
    rw [←hgen]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hn : Q (family P) a ≤ normalizer (V : Set G) :=
    ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)).trans
      (le_normalizer_conjugateSpanBy _ _)
  apply le_antisymm ?_ (sup_le hVQ inf_le_right)
  intro x hx
  have hx' : x ∈ (V : Set G) * (Q (family P) a : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left V (Q (family P) a) hn]
    exact hQsub hx
  obtain ⟨v,hv,y,hy,rfl⟩ := hx'
  have hyQ : y ∈ Q (family P) b := by
    have hh := (Q (family P) b).mul_mem ((Q (family P) b).inv_mem (hVQ hv)) hx
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left hv) (mem_sup_right ⟨hy,hyQ⟩)

/-- A neighboring escaping center supplies the complete Sylow image at a linear vertex. -/
theorem source_linear_center_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k))
    (he : ¬ Z (family P) a ≤ Q (family P) b) :
    (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2 =
      Z (family P) a ⊔ Q (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  apply source_linear_edge_supplement h hB d hab.symm Mb e (Z (family P) a)
    (IsElementaryAbelian.isPGroup 2 _) _ _ he
  · exact le_inf
      (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)))
      (Z_le_stabilizer _ a)
  · exact inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp
      (Z_normal _ a))


/-- At a linear beta vertex, the two literal Chapter 11 seeds generate the full corrected span. -/
theorem source_linear_betaSpan_eq_pairSpan (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k)) :
    betaSpan (stabilizer (family P) b) (Z (family P) a) =
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) := by
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

variable {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]

/-- Source (11.3)(h) for two actual linear quotient markings, at arbitrary binary field sizes. -/
theorem source_linear_pair_core_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k')) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b) := by
  have hh := source_linear_beta_core_generation h hB d hc hb hbc hac Ma Mb ea
  rwa [source_linear_betaSpan_eq_pairSpan h hB d hc hb hbc hac Mb eb] at hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
