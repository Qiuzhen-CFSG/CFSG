module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceTriple
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SeedStructure
public import Theory.Quasithin.EvenCharacteristic

/-!
# Chapter 11 seeds on the actual source graph

The source triple gives elementary centers, core centralization, and mutual
normalization of adjacent cores. Thus (11.1)(c) holds on every edge. Local
transitivity supplies one conjugator for both centers and their core
intersections, identifying the corrected beta span with the neighboring
seed span. Two such seeds have central derived subgroup equal to their
Frattini subgroup. A critical center escapes the core because it escapes
the full local kernel; the two subgroups are never identified.

These are applications of the shared source graph, valid with an infinite
completion and finite vertex stabilizers. The rank-one arguments of
(11.2)--(11.6), including nontriviality of the derived subgroup, remain to
be proved before the profiles (11.7)--(11.8) follow.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.0)--(11.3), printed pp.167--171.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual Sylow-center span is elementary, by its containment in the core omega-center. -/
theorem source_center_elementary (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) : IsElementaryAbelian 2 (Z (family P) v) :=
  IsElementaryAbelian.of_injective (inclusion (source_Z_Q_U h v).1)
    (inclusion_injective _)

/-- The center span is centralized by its own core. -/
theorem source_core_centralizes_center (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    Q (family P) v ≤ centralizer (Z (family P) v : Set G) := by
  apply le_centralizer_iff.mpr
  intro z hz
  exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hz)).2.1

/-- The neighboring core fixes the original vertex and hence normalizes its center span. -/
theorem source_adjacent_core_normalizes_center (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    Q (family P) b ≤ normalizer (Z (family P) a : Set G) := by
  let := finite_endpoints h
  exact ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a))

/-- Source (11.1)(c), with all normalization and exponent premises discharged. -/
theorem source_adjacent_core_center_quadratic (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    ⁅⁅Q (family P) b, Z (family P) a⁆, Z (family P) a⁆ = ⊥ := by
  let := source_center_elementary h a
  exact core_center_quadratic _ _ (source_adjacent_core_normalizes_center h hab)

/-- One element of the beta stabilizer transports the center, the core, and the seed together. -/
theorem source_neighbor_conjugate (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) :
    ∃ g ∈ stabilizer (family P) b,
      (Z (family P) a).map (MulAut.conj g).toMonoidHom = Z (family P) c ∧
      (Q (family P) b).map (MulAut.conj g).toMonoidHom = Q (family P) b ∧
      (Z (family P) a ⊓ Q (family P) b).map (MulAut.conj g).toMonoidHom =
        Z (family P) c ⊓ Q (family P) b := by
  let := finite_endpoints h
  obtain ⟨g,hg,hac⟩ := locally_transitive (family P) hab.symm hbc
  have hz : (Z (family P) a).map (MulAut.conj g).toMonoidHom = Z (family P) c := by
    rw [←Z_translate, hac]
  have hq : (Q (family P) b).map (MulAut.conj g).toMonoidHom = Q (family P) b := by
    rw [←Q_translate]
    rw [show g • b = b from hg]
  exact ⟨g,hg,hz,hq,by rw [map_inf _ _ _ (MulAut.conj g).injective,hz,hq]⟩

/-- The corrected Chapter 11 span is exactly the join of all neighboring intersections. -/
theorem source_betaSpan_eq_neighbor_span (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    betaSpan (stabilizer (family P) b) (Z (family P) a) =
      ⨆ c : (graph (family P)).neighborSet b, Z (family P) c.val ⊓ Q (family P) b := by
  let := finite_endpoints h
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨g,hg,z,hz,rfl⟩
    have hbc : (graph (family P)).Adj b (g • a) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab.symm
      change (graph (family P)).Adj (g • b) (g • a) at hh
      rwa [show g • b = b from hg] at hh
    have hmem : g * z * g⁻¹ ∈ Z (family P) (g • a) ⊓ Q (family P) b := by
      rw [Z_translate]
      refine ⟨mem_map_of_mem _ hz.1, ?_⟩
      have hq := mem_map_of_mem (MulAut.conj g).toMonoidHom hz.2
      change g * z * g⁻¹ ∈ (Q (family P) b).map (MulAut.conj g).toMonoidHom at hq
      rw [←Q_translate,show g • b = b from hg] at hq
      exact hq
    exact (le_iSup (fun c : (graph (family P)).neighborSet b =>
      Z (family P) c.val ⊓ Q (family P) b) ⟨g • a,hbc⟩) hmem
  · apply iSup_le
    intro c
    obtain ⟨g,hg,_,_,he⟩ := source_neighbor_conjugate h hab c.property
    rw [←he]
    rintro x ⟨z,hz,rfl⟩
    exact subset_closure ⟨g,hg,z,hz,rfl⟩

/-- The actual two-seed group has equal derived and Frattini layers, central in that group. -/
theorem source_pairSpan_commutator_frattini (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) :
    let W := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    ⁅W,W⁆ = ⁅Z (family P) a ⊓ Q (family P) b, Z (family P) c ⊓ Q (family P) b⁆ ∧
      (frattini W).map W.subtype = ⁅W,W⁆ ∧
      ⁅W,W⁆ ≤ Z (family P) a ⊓ Z (family P) c ∧ ⁅⁅W,W⁆,W⁆ = ⊥ := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let : Finite (Q (family P) b) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  obtain ⟨hd,hf,hi,hc⟩ := pairSpan_commutator_frattini
    (Z (family P) a) (Z (family P) c) (Q (family P) b)
    (isPGroup_pCoreIn 2 _) (source_adjacent_core_normalizes_center h hab)
    (source_adjacent_core_normalizes_center h hbc.symm)
  exact ⟨hd,hf.trans hd.symm,hi,hc⟩

/-- Both chosen seeds occur in the full corrected beta span. -/
theorem source_pairSpan_le_betaSpan (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) :
    pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ≤
      betaSpan (stabilizer (family P) b) (Z (family P) a) := by
  rw [source_betaSpan_eq_neighbor_span h hab]
  exact sup_le (le_iSup_of_le (⟨a,hab.symm⟩ : (graph (family P)).neighborSet b) le_rfl)
    (le_iSup_of_le (⟨c,hbc⟩ : (graph (family P)).neighborSet b) le_rfl)

/-- Identifying the two-seed group with the core also identifies the full corrected span. -/
theorem source_betaSpan_eq_core_of_pairSpan (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hpair : pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) =
      Q (family P) b) :
    betaSpan (stabilizer (family P) b) (Z (family P) a) = Q (family P) b := by
  exact le_antisymm (betaSpan_le_core _ _)
    (hpair ▸ source_pairSpan_le_betaSpan h hab hbc)

/-- Adjacent cores normalize one another, relative to the opposite vertex stabilizer. -/
theorem source_adjacent_core_normalizes_core (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    Q (family P) a ≤ normalizer (Q (family P) b : Set G) := by
  have hn : stabilizer (family P) b ≤ normalizer (Q (family P) b : Set G) := by
    simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 (stabilizer (family P) b)).le_normalizer_map
        (stabilizer (family P) b).subtype
  exact ((source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab).trans inf_le_right)).trans hn

/-- The commutator of adjacent cores lies in their literal intersection. -/
theorem source_adjacent_core_commutator (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    ⁅Q (family P) a,Q (family P) b⁆ ≤ Q (family P) a ⊓ Q (family P) b :=
  le_inf (le_normalizer_iff_commutator_le_left.mp
    (source_adjacent_core_normalizes_core h hab.symm))
    (le_normalizer_iff_commutator_le_right.mp
      (source_adjacent_core_normalizes_core h hab))

/-- Characteristic two transports to every vertex stabilizer. -/
theorem source_vertex_core_selfCentralizing (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    centralizer (pCore 2 (stabilizer (family P) v) : Set (stabilizer (family P) v)) ≤
      pCore 2 (stabilizer (family P) v) := by
  have hbase (i : Bool) : centralizer (pCore 2 (family P i) : Set (family P i)) ≤
      pCore 2 (family P i) := by
    cases i
    · exact source_core_selfCentralizing (Classical.choice (h.local_data 0))
    · exact source_core_selfCentralizing (Classical.choice (h.local_data 1))
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  rw [←hg,stabilizer_translate]
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) _).mpr
  change centralizer (pCore 2 (MulAction.stabilizer G
    (Subgroup.CosetGeometry.base (family P) v.type)) : Set (MulAction.stabilizer G
      (Subgroup.CosetGeometry.base (family P) v.type))) ≤
    pCore 2 (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) v.type))
  rw [Subgroup.CosetGeometry.stabilizer_base]
  exact hbase v.type

/-- The ambient centralizer bound retains the intersection with the vertex stabilizer. -/
theorem source_core_selfCentralizing_in_vertex (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    stabilizer (family P) v ⊓ centralizer (Q (family P) v : Set G) ≤ Q (family P) v := by
  intro x hx
  have hxc : (⟨x,hx.1⟩ : stabilizer (family P) v) ∈
      centralizer (pCore 2 (stabilizer (family P) v) : Set (stabilizer (family P) v)) := by
    intro y hy
    exact Subtype.ext (hx.2 y.val (mem_map_of_mem _ hy))
  exact mem_map_of_mem (stabilizer (family P) v).subtype
    (source_vertex_core_selfCentralizing h v hxc)

/-- A critical pair at distance one is an actual edge. -/
theorem source_critical_one_adjacent
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) : (graph (family P)).Adj a b :=
  SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)

/-- A critical center distinguishes the Chapter 11 span from the unrestricted conjugate span. -/
theorem source_critical_span_ne_unrestricted (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b) :
    betaSpan (stabilizer (family P) b) (Z (family P) a) ≠
      conjugateSpanBy (Z (family P) a) (stabilizer (family P) b) := by
  apply betaSpan_ne_unrestricted
  exact fun hZ => hc.2 (hZ.trans (source_Z_Q_U h b).2)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
