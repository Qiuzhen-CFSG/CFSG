module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CenterDisjointness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualGeneration

/-!
# The opposite residual moves the terminal-center intersection

At distance three, the nonzero subgroup H intersect Z_alpha' cannot
centralize O²(L_beta). If it did, X = O²(L_beta) Q_(alpha+2) would
normalize it. The two-edge normalizer argument, using both local
transitivity witnesses, makes the middle core a Sylow subgroup of X.
But X is normal in L_beta, so it contains the normal closure of that
core, contradicting the earlier 6.5 core-span obstruction.

This is the geometric end of DGS 8.5 with the literal residual, original
cores and relative normality. It is independent of naturality, field size
and the 8.6 central-containment conclusion. The separate natural-module
calculation must still place H in the residual-fixed denominator before
this contradiction proves opposite nonnaturality.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.5, printed p.139. `OppositeResidualApplication` applies this to the
original reduced critical configuration and discharges distance three
for all five small terminal models.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The geometric contradiction at the end of 8.5, on the literal two-edge
path: a nonzero normal subgroup of the terminal center cannot be centralized
by the opposite residual. -/
theorem source_central_endpoint_not_residual_fixed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hwz : (graph (family P)).Adj w z) (hvz : v ≠ z)
    (Mv : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (Mw : IsRankOneModel (d.localGroup w ⧸ pCore 2 (d.localGroup w)))
    (he : ¬ Q (family P) w ≤ Q (family P) v)
    (hz : Z (family P) z = omegaCenterIn (d.localGroup z))
    (H : Subgroup G) (hHZ : H ≤ Z (family P) z) (hne : H ≠ ⊥)
    (hn : d.localGroup z ≤ normalizer (H : Set G)) :
    ¬ H ≤ centralizer (((pResidual 2 (d.localGroup v)).map
      (d.localGroup v).subtype : Subgroup G) : Set G) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let E := (pResidual 2 L).map L.subtype
  let X := E ⊔ Q F w
  let C := conjugateSpanBy (Q F w) L
  intro hfixed
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw.symm
  obtain ⟨hXL,hnX,_,_⟩ := source_residual_join_sylow h hB d hvw R hR
  change X ≤ L at hXL
  change L ≤ normalizer (X : Set G) at hnX
  have hQwLz : Q F w ≤ d.localGroup z := by
    obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hwz.symm
    have hh := Noncommuting.graph_Q_le_edgeCore h hwz
    rw [inf_comm,←hT] at hh
    exact hh.trans (map_subtype_le _)
  have hQH : Q F w ≤ centralizer (H : Set G) := by
    apply le_centralizer_iff.mp
    intro x hx y hy
    have hxO : x ∈ omegaCenterIn (d.localGroup z) := hz ▸ hHZ hx
    exact ((mem_omegaCenterIn_iff _ _).mp hxO).2.1 y (hQwLz hy)
  have hXH : X ≤ normalizer (H : Set G) := by
    apply sup_le
    · exact (le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)
    · exact hQH.trans (Subgroup.centralizer_le_normalizer _)
  have hHedge : H ≤ stabilizer F w ⊓ stabilizer F z := by
    apply le_inf
    · exact hHZ.trans (((source_Z_Q_U h z).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h z).2.trans ((ballKernel_one_le_edge F hwz.symm).trans inf_le_right)))
    · exact hHZ.trans (Z_le_stabilizer F z)
  obtain ⟨S,hS⟩ := source_core_sylow_of_normalizing_subgroup h hB d hvw hwz hvz
    Mv Mw X H hXL le_sup_right he hHedge hne hn hXH
  have hQC : Q F w ≤ C := le_conjugateSpanBy _ _
  have hCX : C ≤ X := conjugateSpanBy_le le_sup_right hnX
  have hSR : (S : Subgroup X) ≤ (inclusion hCX).range := by
    intro x hx
    exact ⟨⟨x,hQC (hS ▸ mem_map_of_mem X.subtype hx)⟩,rfl⟩
  apply d.core_span_obstruction v w hvw
  refine ⟨S.comapOfInjective (inclusion hCX) (inclusion_injective _) hSR,?_⟩
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hm := mem_map_of_mem X.subtype
      (show inclusion hCX x ∈ (S : Subgroup X) from hx)
    rw [hS] at hm
    exact hm
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hS.symm ▸ hx
    exact ⟨⟨y,hQC (hS ▸ mem_map_of_mem X.subtype hy)⟩,hy,rfl⟩

/-- On the actual distance-three critical path, even the nonzero part of H
in Z_alpha' is moved by O²(L_beta). Thus the literal residual denominator
cannot contain H. No naturality or 8.6 central-containment premise is used. -/
theorem source_distance_three_critical_commutator_not_residual_fixed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer
        ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : b (family P) = 3) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥) :
    let F := family P
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    let E := (pResidual 2 (d.localGroup beta)).map (d.localGroup beta).subtype
    (¬ H ⊓ Z F a' ≤ centralizer (E : Set G)) ∧
      ¬ H ≤ V F beta 1 ⊓ centralizer (E : Set G) := by
  let := finite_endpoints h
  let F := family P
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let L := d.localGroup a'
  have hb1 : 1 < b F := by change 1 < b (family P); omega
  obtain ⟨_,_,_,_,mid,hm,hdm,_,_⟩ := source_critical_geometry h d hc hab hd hb1 hcomm
  have hbm : (graph F).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by
    change (graph (family P)).dist beta mid = 1
    omega)
  have hbne : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self] at hd
    omega
  have hcentral := critical_end_center_of_commuting F h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2)
    hc hcomm L (d.sylow_or_center a')
  have hmeet := source_critical_commutator_meets_terminal_center h hB d models
    hc hab hd hb1 hcomm hne
  obtain ⟨hn,hHZ,_⟩ := source_critical_commutator_structure h hB d hc hab hd hb1 hcomm models
  have hHL : H ≤ L := (hHZ ⟨mid,hm⟩).trans
    (((Z_neighbor_le_V F hm).trans
      (V_le_Q_of_dist_add_lt_b F h.generate (fun v => (source_Z_Q_U h v).1)
        a' a' 1 (by simpa using hb1) (d.kernel_sylow a'))).trans
        ((pCoreIn_le_sylow (stabilizer F a') default).trans (d.sylow_le a' default)))
  have hnH : L ≤ normalizer (H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hHL).mp hn
  have hnHZ : L ≤ normalizer ((H ⊓ Z F a' : Subgroup G) : Set G) :=
    (le_inf hnH ((d.local_le a').trans (stabilizer_normalizes_Z F a'))).trans
      inf_normalizer_le_normalizer_inf
  have he : ¬ Q F mid ≤ Q F beta := by
    intro hh
    apply hob mid beta hbm.symm
    change stabilizer F mid ≤ normalizer ((Q F beta ⊓ Q F mid : Subgroup G) : Set G)
    rw [inf_eq_right.mpr hh]
    exact stabilizer_normalizes_Q F mid
  have hmove := source_central_endpoint_not_residual_fixed h hB d hbm hm.symm hbne
    (models beta) (models mid) he hcentral (H ⊓ Z F a') inf_le_right hmeet hnHZ
  exact ⟨hmove,fun hh => hmove (inf_le_left.trans (hh.trans inf_le_right))⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
