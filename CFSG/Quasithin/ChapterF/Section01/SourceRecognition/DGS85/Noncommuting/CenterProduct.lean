module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CenterTypes

/-!
# Applying the exact center-product conclusion of DGS (6.6)

The source theorem does not unconditionally forbid a normal adjacent center
product: it says that such normality makes Z_delta the omega-center of an edge
Sylow. In the epsilon-one branch, (6.2)(c) makes Q_delta Sylow in its local
centralizer. The edge Sylow would then lie in Q_delta, contrary to the actual
rank-one quotient. This proves the obstruction needed by (7.2) from the exact
earlier-source conclusion, preserving relative normality and the full edge.

Source: DGS, *Groups and Graphs* (1985), (6.6), p.123, and (7.2)--(7.3), p.127.
-/

public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- In the actual rank-one local data the vertex core is strictly smaller
than the edge Sylow; a normal Sylow would contradict its proper normalizer. -/
theorem local_edgeCore_not_le_vertexCore {H E : Subgroup G} (d : LocalRankOneData H E)
    (hodd : ¬ 2 ∣ d.Pstar.relIndex H)
    (hclosed : ∃ T : Sylow 2 E, (T : Subgroup E) = pCore 2 E) :
    ¬ E.pCoreIn 2 ≤ H.pCoreIn 2 := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  intro hle
  have he := local_sylow_eq_edgeCore d hodd hclosed
  have hc : d.Pstar.pCoreIn 2 = H.pCoreIn 2 := d.same_core
  have hT : (d.sylow : Subgroup d.Pstar) = pCore 2 d.Pstar := by
    apply le_antisymm ?_ (pCore_isPGroup.le_sylow_of_normal d.sylow)
    intro t ht
    have hm := hle (he ▸ mem_map_of_mem d.Pstar.subtype ht)
    rw [← hc] at hm
    obtain ⟨x,hx,hxt⟩ := hm
    exact d.Pstar.subtype_injective hxt ▸ hx
  have hproper := (rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).proper
  change normalizer ((d.sylow : Subgroup d.Pstar) : Set d.Pstar) < ⊤ at hproper
  rw [hT,normalizer_eq_top] at hproper
  exact (lt_irrefl _ hproper)

/-- The Sylow-centralizer alternative in (6.2)(c) excludes equality with
the literal omega-center of the edge Sylow. -/
theorem graph_seed_ne_of_centralizerSylow
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (d : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (hodd : ¬ 2 ∣ d.Pstar.relIndex (stabilizer (family P) v))
    (hCS : Stellmacher.IsSylowSubgroupIn (Q (family P) v)
      (d.Pstar ⊓ centralizer (Z (family P) v : Set G))) :
    Z (family P) v ≠ Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2) := by
  intro hseed
  let E := stabilizer (family P) v ⊓ stabilizer (family P) u
  let T := E.pCoreIn 2
  have hclosed := source_edge_core_sylow h hB he
  have hTL : T ≤ d.Pstar := by
    rw [show T = (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype from
      (local_sylow_eq_edgeCore d hodd hclosed).symm]
    exact map_subtype_le _
  have hTC : T ≤ centralizer (Z (family P) v : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz t ht
    rw [hseed] at hz
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz |>.2.2 t ht
  have hQN : Q (family P) v ≤ d.Pstar ⊓ centralizer (Z (family P) v : Set G) := by
    obtain ⟨S,hS⟩ := hCS
    rw [← hS]
    exact map_subtype_le _
  have hNQ : d.Pstar ⊓ centralizer (Z (family P) v : Set G) ≤
      normalizer (Q (family P) v : Set G) :=
    (inf_le_left.trans d.Pstar_le).trans ((stabilizer (family P) v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hi := inf_eq_inf_of_normal_sylow T _ _ (isPGroup_pCoreIn 2 E) hQN hNQ hCS
  rw [inf_of_le_left (le_inf hTL hTC)] at hi
  exact local_edgeCore_not_le_vertexCore d hodd hclosed (hi.le.trans inf_le_right)

/-- The literal (6.6) seed equality contradicts the noncentral alternative
of (6.2)(c), using the same edge two-core and marked rank-one local actor. -/
theorem graph_center_product_obstruction
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (d : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (hodd : ¬ 2 ∣ d.Pstar.relIndex (stabilizer (family P) v))
    (hCS : Stellmacher.IsSylowSubgroupIn (Q (family P) v)
      (d.Pstar ⊓ centralizer (Z (family P) v : Set G)))
    (h66 : stabilizer (family P) v ≤
        normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G) →
      Z (family P) v = Stellmacher.omegaOneCenterAmbient
        ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2)) :
    ¬ stabilizer (family P) v ≤
      normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G) := by
  intro hn
  exact graph_seed_ne_of_centralizerSylow h hB he d hodd hCS (h66 hn)

/-- The omega-center of the marked local actor lies in the omega-center of
its literal edge Sylow. Only relative centrality is used. -/
theorem local_omega_le_edgeSeed {H E : Subgroup G} (d : LocalRankOneData H E)
    (hodd : ¬ 2 ∣ d.Pstar.relIndex H)
    (hclosed : ∃ T : Sylow 2 E, (T : Subgroup E) = pCore 2 E) :
    Stellmacher.omegaOneCenterAmbient d.Pstar ≤
      Stellmacher.omegaOneCenterAmbient (E.pCoreIn 2) := by
  let O := Stellmacher.omegaOneCenterAmbient d.Pstar
  let : IsElementaryAbelian 2 O := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let T := (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype
  have hOL : O ≤ d.Pstar := fun x hx =>
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx |>.1
  have hOC : O ≤ centralizer (T : Set G) := by
    intro x hx t ht
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.2 t (map_subtype_le _ ht)
  have hOT : O ≤ T := le_sylow_image_of_normalizes d.Pstar d.sylow rfl
    (IsElementaryAbelian.isPGroup 2 O) hOL (hOC.trans (Subgroup.centralizer_le_normalizer _))
  rw [← local_sylow_eq_edgeCore d hodd hclosed]
  intro x hx
  apply (Stellmacher.mem_omegaOneCenterAmbient_iff T x).mpr
  exact ⟨hOT hx,(Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.1,hOC hx⟩

private theorem seed_le_centerSpan (H : Subgroup G) (S : Sylow 2 H) :
    Stellmacher.omegaOneCenterAmbient ((S : Subgroup H).map H.subtype) ≤
      Theory.GroupTheory.AmalgamGraph.sylowCenterSpan H :=
  le_iSup (fun T : Sylow 2 H =>
    Stellmacher.omegaOneCenterAmbient ((T : Subgroup H).map H.subtype)) S

/-- The full vertex center span contains the omega-center of the same edge
Sylow. The marked local Sylow is lifted by the actual odd relative index. -/
theorem graph_edgeSeed_le_Z
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (d : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (hodd : ¬ 2 ∣ d.Pstar.relIndex (stabilizer (family P) v)) :
    Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2) ≤ Z (family P) v := by
  let : Finite (stabilizer (family P) v) := d.finite_P
  have heq := local_sylow_eq_edgeCore d hodd (source_edge_core_sylow h hB he)
  have hs : Stellmacher.IsSylowSubgroupIn
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2) d.Pstar :=
    ⟨d.sylow,heq⟩
  obtain ⟨S,hS⟩ := sylow_in_overgroup_of_odd_relIndex (stabilizer (family P) v)
    d.Pstar ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2) d.Pstar_le hs hodd
  change Stellmacher.omegaOneCenterAmbient _ ≤
    Theory.GroupTheory.AmalgamGraph.sylowCenterSpan (stabilizer (family P) v)
  rw [← hS]
  exact seed_le_centerSpan _ S

/-- The source epsilon-one hypothesis concerns Omega_1(Z(S)) for the full
edge Sylow. It implies the noncentral-center condition used in (6.2)(c). -/
theorem graph_noncentral_of_edgeSeed_ne
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (d : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (hodd : ¬ 2 ∣ d.Pstar.relIndex (stabilizer (family P) v))
    (hne : Z (family P) v ≠ Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2)) :
    Z (family P) v ≠ Stellmacher.omegaOneCenterAmbient d.Pstar := by
  intro hz
  apply hne
  exact le_antisymm (hz ▸ local_omega_le_edgeSeed d hodd (source_edge_core_sylow h hB he))
    (graph_edgeSeed_le_Z h hB he d hodd)

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
