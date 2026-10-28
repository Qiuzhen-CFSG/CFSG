module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SeedEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration

/-!
# Critical seed escape for all source rank-one rows

An elementary subgroup escaping the vertex two-core determines its containing
Sylow in the actual local quotient. Since an edge Sylow fixes only its marked
neighbor, the elementary subgroup does too. Two distinct neighboring critical
centers therefore cannot generate a two-group. The quadratic core argument
then proves (11.2)(c) and nonzero movement of the seed, without a cubic-valence
assumption. An escaping elementary subgroup together with a different edge
Sylow generates the intrinsic local group; this applies to the same seed.

The earlier local-group data and their actual quotient models remain explicit
Chapter 6 inputs. All five rank-one alternatives are retained, with separate
special and projective unitary markings. The pair here contains unrestricted
centers; the seed remains Z_alpha intersect Q_beta, as Chapter 11 requires.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)(c), p.168, and the rank-one Sylow properties (5.1), pp.104--105.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem sylow_eq_of_escape (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R T : Sylow 2 (d.localGroup v)) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A ≤ (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype)
    (hAT : A ≤ (T : Subgroup (d.localGroup v)).map (d.localGroup v).subtype)
    (he : ¬ A ≤ Q (family P) v) : R = T := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  have hAL : A ≤ L := hAR.trans (map_subtype_le _)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  apply local_sylow_eq_of_elementary_escape M R T (A.subgroupOf L)
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hAR hx
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hAT hx
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro hh
    apply he
    intro x hx
    rw [← localGroup_core_eq (family P) d v]
    exact ⟨⟨x, hAL hx⟩, hh hx, rfl⟩

/-- An elementary subgroup escaping the actual core fixes at most one neighbor. -/
theorem source_elementary_escape_unique_neighbor (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v a c : Vertex (family P)} (hva : (graph (family P)).Adj v a)
    (hvc : (graph (family P)).Adj v c)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAv : A ≤ stabilizer (family P) v) (hAa : A ≤ stabilizer (family P) a)
    (hAc : A ≤ stabilizer (family P) c) (he : ¬ A ≤ Q (family P) v) : c = a := by
  let := finite_endpoints h
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hva
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hvc
  have hAcore {z : Vertex (family P)} (hvz : (graph (family P)).Adj v z)
      (hAz : A ≤ stabilizer (family P) z) :
      A ≤ (stabilizer (family P) v ⊓ stabilizer (family P) z).pCoreIn 2 := by
    let E := stabilizer (family P) v ⊓ stabilizer (family P) z
    let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) v from inf_le_left))
      (inclusion_injective _)
    exact pGroup_le_core_of_core_sylow E A (le_inf hAv hAz)
      (IsElementaryAbelian.isPGroup 2 A) (source_edge_core_sylow h hB hvz)
  have hRT := sylow_eq_of_escape h d v M R T A
    (hR ▸ hAcore hva hAa) (hT ▸ hAcore hvc hAc) he
  apply source_edge_sylow_unique_neighbor h d hva hvc M R hR
  rw [hRT,hT]
  exact (pCoreIn_le 2 _).trans inf_le_right

private theorem neighbor_escape (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (he : ¬ Z (family P) a ≤ U (family P) b) :
    ¬ Z (family P) c ≤ Q (family P) b := by
  let := finite_endpoints h
  obtain ⟨g,hg,hz,hq,_⟩ := source_neighbor_conjugate h hab hbc
  intro hh
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
  have hz' : (Z (family P) c).map (MulAut.conj g⁻¹).toMonoidHom = Z (family P) a := by
    rw [←hz,←Z_translate,←Z_translate,inv_smul_smul]
  have hq' : (Q (family P) b).map (MulAut.conj g⁻¹).toMonoidHom = Q (family P) b := by
    rw [←Q_translate,show g⁻¹ • b = b from (stabilizer (family P) b).inv_mem hg]
  rw [hz',hq'] at hm
  exact he (hm.trans (source_Z_Q_U h b).2)

/-- Distinct neighboring critical centers never generate a two-group in any of the source rank-one rows. -/
theorem source_rankOne_centers_not_isPGroup (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (M : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    ¬ IsPGroup 2 (Z (family P) a ⊔ Z (family P) c : Subgroup G) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  have hab := source_critical_one_adjacent hc hb
  have hZa : Z (family P) a ≤ stabilizer (family P) b :=
    (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans (source_Z_Q_U h a).2).trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right)
  have hZc : Z (family P) c ≤ stabilizer (family P) b :=
    (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans (source_Z_Q_U h c).2).trans
      ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hab.symm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hbc
  have hRZa : Z (family P) a ≤ (R : Subgroup (d.localGroup b)).map (d.localGroup b).subtype := by
    rw [hR]
    exact ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab)
  have hTZc : Z (family P) c ≤ (T : Subgroup (d.localGroup b)).map (d.localGroup b).subtype := by
    rw [hT]
    exact ((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
      (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hbc.symm)
  intro hp
  let W := Z (family P) a ⊔ Z (family P) c
  have hWL : W ≤ d.localGroup b :=
    pGroup_le_localGroup (family P) d b W hp (sup_le hZa hZc)
  obtain ⟨V,hV⟩ := (hp.comap_subtype (K := d.localGroup b)).exists_le_sylow
  have hWV : W ≤ (V : Subgroup (d.localGroup b)).map (d.localGroup b).subtype := by
    intro x hx
    exact ⟨⟨x,hWL hx⟩,hV hx,rfl⟩
  have hRV := sylow_eq_of_escape h d b M R V (Z (family P) a)
    hRZa (le_sup_left.trans hWV) (fun he => hc.2 (he.trans (source_Z_Q_U h b).2))
  have hTV := sylow_eq_of_escape h d b M T V (Z (family P) c)
    hTZc (le_sup_right.trans hWV) (neighbor_escape h hab hbc hc.2)
  apply hac
  symm
  apply source_edge_sylow_unique_neighbor h d hab.symm hbc M R hR
  rw [hRV,←hTV,hT]
  exact (pCoreIn_le 2 _).trans inf_le_right

/-- DGS (11.2)(c) for all the actual rank-one quotient alternatives. -/
theorem source_rankOne_seed_escape (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (M : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    ¬ Z (family P) a ⊓ Q (family P) b ≤ Q (family P) c ∧
      ⁅Z (family P) a ⊓ Q (family P) b,Z (family P) c⁆ ≠ ⊥ := by
  have hn := source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac M
  exact ⟨source_seed_not_le_opposite_core h (source_critical_one_adjacent hc hb) hbc hn,
    source_seed_commutator_ne_bot h (source_critical_one_adjacent hc hb) hbc hn⟩
/-- An escaping elementary subgroup and the edge radical at another neighbor
 generate the actual local actor, through its literal rank-one quotient. -/
theorem source_elementary_escape_edge_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v a c : Vertex (family P)} (hva : (graph (family P)).Adj v a)
    (hvc : (graph (family P)).Adj v c) (hac : a ≠ c)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAv : A ≤ stabilizer (family P) v) (hAa : A ≤ stabilizer (family P) a)
    (he : ¬ A ≤ Q (family P) v) :
    A ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) c).pCoreIn 2 =
      d.localGroup v := by
  let := finite_endpoints h
  let L := d.localGroup v
  let E := stabilizer (family P) v ⊓ stabilizer (family P) c
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  have hAL : A ≤ L := pGroup_le_localGroup (family P) d v A
    (IsElementaryAbelian.isPGroup 2 A) hAv
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hvc
  have hEL : E.pCoreIn 2 ≤ L := hT ▸ map_subtype_le _
  apply le_antisymm (sup_le hAL hEL)
  rcases relative_rankOne_overgroup L (A ⊔ E.pCoreIn 2)
    ((sup_le hAL hEL).trans L.le_normalizer) T
    (fun H hTH hn => (rankOneSylowFacts_of_quotient T
      (M.rankOneSylowFacts _)).unique_maximal H hTH (lt_top_iff_ne_top.mpr hn))
    (hT ▸ le_sup_right) with hle | hn
  · exact hle
  · exfalso
    apply hac
    symm
    apply source_elementary_escape_unique_neighbor h hB d hva hvc M A hAv hAa _ he
    intro x hx
    exact ((source_edge_local_normalizer h d hvc M T hT).1.le
      ⟨hAv hx,hn (mem_sup_left hx)⟩).2

/-- The escaping Chapter 11 seed supplies the full local generation at the
 opposite endpoint with every edge Sylow other than the original one. -/
theorem source_rankOne_seed_edge_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c w : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcw : (graph (family P)).Adj c w) (hbw : b ≠ w)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (Mc : IsRankOneModel (d.localGroup c ⧸ pCore 2 (d.localGroup c))) :
    (Z (family P) a ⊓ Q (family P) b) ⊔
      (stabilizer (family P) c ⊓ stabilizer (family P) w).pCoreIn 2 = d.localGroup c := by
  let := source_center_elementary h a
  let : IsElementaryAbelian 2 (Z (family P) a ⊓ Q (family P) b : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  apply source_elementary_escape_edge_generation h hB d hbc.symm hcw hbw Mc _
  · exact (inf_le_right.trans (source_Z_Q_U h b).2).trans
      ((ballKernel_one_le_edge _ hbc).trans inf_le_right)
  · exact inf_le_right.trans (Q_le_stabilizer _ b)
  · exact (source_rankOne_seed_escape h hB d hc hb hbc hac Mb).1
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
