module
public import Theory.GroupTheory.SemidihedralNormalTower
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration

/-!
# The predecessor normality tower at critical distance three

At b = 3 the predecessor of the terminal vertex is adjacent to beta.
Its core fixes beta, so it normalizes the whole neighboring span V_beta.
The original terminal edge Sylow normalizes that predecessor core.
Pass both containments and both normalizer relations through the literal
terminal quotient map to obtain E normal in A normal in S. If S has the
marked SD16 presentation and E has order two, the semidihedral normal-tower
theorem makes E central in S.

The argument uses only the original earlier geometric interfaces and b = 3;
no rank-one model for the terminal quotient or moving-edge generation is
assumed. Thus it applies to the order-144 setup branch whenever b = 3 has
been established independently. It does not assert b = 3 in that branch,
or supply predecessor normalization at larger distance.

Source: DGS, *Groups and Graphs* (1985), 8.1(a,d,e,g), pp.132--133.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- At distance three the literal predecessor-core image is normal in the
terminal Sylow image and normalizes the entire neighboring-span image.
No rank-one quotient catalogue or moving-edge generation is used. -/
theorem source_distance_three_predecessor_image_normality
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : b (family P) = 3) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥) :
    ∃ prev : Vertex (family P), (graph (family P)).Adj a' prev ∧
      (graph (family P)).Adj beta prev ∧
      V (family P) beta 1 ≤ Q (family P) prev ∧
      Q (family P) prev ≤ normalizer (V (family P) beta 1 : Set G) ∧
      ∃ R : Sylow 2 (d.localGroup a'),
        (R : Subgroup (d.localGroup a')).map (d.localGroup a').subtype =
          (stabilizer (family P) a' ⊓ stabilizer (family P) prev).pCoreIn 2 ∧
        let L := d.localGroup a'
        let q := QuotientGroup.mk' (pCore 2 L)
        let E := ((V (family P) beta 1).subgroupOf L).map q
        let A := ((Q (family P) prev).subgroupOf L).map q
        let S := (R : Subgroup L).map q
        E ≤ A ∧ A ≤ S ∧ (E.subgroupOf A).Normal ∧ (A.subgroupOf S).Normal := by
  let := finite_endpoints h
  let F := family P
  obtain ⟨_,_,_,_,prev,hp,hdp,hAP,_⟩ := source_critical_geometry h d hc hab hd (by omega) hcomm
  have hbp : (graph F).Adj beta prev := SimpleGraph.dist_eq_one_iff_adj.mp (by
    change (graph (family P)).dist beta prev = 1
    omega)
  have hQN : Q F prev ≤ normalizer (V F beta 1 : Set G) :=
    ((source_Z_Q_U h prev).2.trans
      ((ballKernel_one_le_edge F hbp.symm).trans inf_le_right)).trans
      (stabilizer_normalizes_V F beta 1)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hp
  refine ⟨prev,hp,hbp,hAP,hQN,R,hR,?_⟩
  let L := d.localGroup a'
  let q := QuotientGroup.mk' (pCore 2 L)
  let E₀ := (V F beta 1).subgroupOf L
  let A₀ := (Q F prev).subgroupOf L
  have hAR : A₀ ≤ R := by
    intro x hx
    have hx' : (x : G) ∈ (R : Subgroup L).map L.subtype := by
      rw [hR]
      have hh := Noncommuting.graph_Q_le_edgeCore h hp.symm
      rw [inf_comm] at hh
      exact hh hx
    obtain ⟨y,hy,he⟩ := hx'
    exact (Subtype.ext he : y = x) ▸ hy
  have hAE : A₀ ≤ normalizer (E₀ : Set L) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    exact le_normalizer_iff.mp hQN a ha x hx
  have hRA : (R : Subgroup L) ≤ normalizer (A₀ : Set L) := by
    apply le_normalizer_iff.mpr
    intro r hr x hx
    have hrp : (r : G) ∈ stabilizer F prev := by
      have hh := mem_map_of_mem L.subtype hr
      rw [hR] at hh
      exact (pCoreIn_le 2 _ hh).2
    exact le_normalizer_iff.mp (stabilizer_normalizes_Q F prev) r hrp x hx
  exact ⟨map_mono (comap_mono hAP),map_mono hAR,
    normal_subgroupOf_of_le_normalizer ((map_mono hAE).trans (E₀.le_normalizer_map q)),
    normal_subgroupOf_of_le_normalizer ((map_mono hRA).trans (A₀.le_normalizer_map q))⟩


/-- The preceding tower centralizes the terminal Sylow whenever its literal
image is SD16 and the neighboring-span image has order two. The source
configuration supplies both normality steps; the displayed generators
mark only the terminal Sylow image. -/
theorem source_distance_three_predecessor_image_centrality
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : b (family P) = 3) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥) :
    ∃ prev : Vertex (family P), (graph (family P)).Adj a' prev ∧
      (graph (family P)).Adj beta prev ∧
      V (family P) beta 1 ≤ Q (family P) prev ∧
      Q (family P) prev ≤ normalizer (V (family P) beta 1 : Set G) ∧
      ∃ R : Sylow 2 (d.localGroup a'),
        (R : Subgroup (d.localGroup a')).map (d.localGroup a').subtype =
          (stabilizer (family P) a' ⊓ stabilizer (family P) prev).pCoreIn 2 ∧
        let L := d.localGroup a'
        let q := QuotientGroup.mk' (pCore 2 L)
        let E := ((V (family P) beta 1).subgroupOf L).map q
        let A := ((Q (family P) prev).subgroupOf L).map q
        let S := (R : Subgroup L).map q
        E ≤ A ∧ A ≤ S ∧
          ∀ s t : S, orderOf s = 8 → orderOf t = 2 → t*s*t⁻¹ = s^3 →
            closure ({s,t} : Set S) = ⊤ → Nat.card E = 2 →
            E ≤ centralizer (S : Set (L ⧸ pCore 2 L)) := by
  obtain ⟨prev,hp,hbp,hAP,hQN,R,hR,hEA,hAS,hEN,hAN⟩ :=
    source_distance_three_predecessor_image_normality h hB d hc hab hd hb hcomm
  refine ⟨prev,hp,hbp,hAP,hQN,R,hR,hEA,hAS,?_⟩
  intro s t hs ht hst hgen hcard
  exact Semidihedral.two_step_normal_order_two_centralizes_sixteen _ _ _ hEA hAS
    ((normal_subgroupOf_iff_le_normalizer hEA).mp hEN)
    ((normal_subgroupOf_iff_le_normalizer hAS).mp hAN) s t hs ht hst hgen hcard

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
