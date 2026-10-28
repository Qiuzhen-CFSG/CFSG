module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicLocalGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking

/-!
# Intrinsic edge cores and local generation

The full Borel-core normalizer, proved from the original starred data,
identifies the unique neighbor fixed by each edge core. Distinct edge
cores therefore escape one another's edges. The original starred
Sylow-overgroup theorem then makes their join the actual local group.
The normalizer formula retains the literal local Sylow inclusion, and
intersecting the two edge omega-centers gives a subgroup of the local
omega-center.

These are the local generation and normalizer facts used in the Chapter 8
central-neighbor argument. They require no marking of the enlarged
quotient, including in the possible order-144 PSU₃(2) enlargement. They
do not prove that remaining enlargement is a rank-one model. Only vertex
stabilizers are finite; the completion and graph need not be finite.
Source: DGS, *Groups and Graphs* (1985), Hypotheses A/B, pp.94--96,
6.0--6.2, pp.118--119, and the use of distinct local Sylows in 8.6, p.139.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full edge core fixes just its own neighbor. -/
theorem graph_intrinsic_edgeCore_unique_neighbor (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z)
    (hle : (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ≤
      stabilizer (family P) z) : w = z := by
  let := finite_endpoints h
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  let D := stabilizer (family P) v ⊓ stabilizer (family P) z
  let : Finite D := Finite.of_injective
    (inclusion (show D ≤ stabilizer (family P) v from inf_le_left)) (inclusion_injective _)
  let R := E.pCoreIn 2
  let T := D.pCoreIn 2
  let : Finite T := Finite.of_injective (inclusion (pCoreIn_le 2 D)) (inclusion_injective _)
  let : Finite R := Finite.of_injective
    (inclusion ((pCoreIn_le 2 E).trans inf_le_left)) (inclusion_injective _)
  obtain ⟨g,hg,hgz⟩ := locally_transitive (family P) hw hz
  have hm : E.map (MulAut.conj g).toMonoidHom = D := by
    rw [show E = stabilizer (family P) v ⊓ stabilizer (family P) w from rfl,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← stabilizer_translate,
      ← stabilizer_translate]
    rw [show g • v = v from hg,hgz]
  have hRT : R.map (MulAut.conj g).toMonoidHom = T := by
    rw [← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj g).injective,hm]
  have hle' : R ≤ T := pGroup_le_core_of_core_sylow D R
    (le_inf ((pCoreIn_le 2 E).trans inf_le_left) hle) (isPGroup_pCoreIn 2 E)
    (source_edge_core_sylow h hB hz)
  have heq : R = T := eq_of_le_of_card_ge hle' (by
    rw [←hRT,card_map_of_injective (MulAut.conj g).injective])
  have hgn : g ∈ normalizer (R : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (hRT.trans heq.symm)
  have hgw : g ∈ stabilizer (family P) v ⊓ stabilizer (family P) w := by
    rw [←source_edge_core_normalizer h hB hw]
    exact ⟨hg,hgn⟩
  exact hgw.2.symm.trans hgz

/-- The literal local point stabilizer is the normalizer of its edge Sylow. -/
theorem graph_intrinsic_edge_sylow_normalizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v w : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (R : Sylow 2 (graphLocalGroup (family P) v))
    (hR : (R : Subgroup (graphLocalGroup (family P) v)).map
      (graphLocalGroup (family P) v).subtype =
        (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2) :
    (stabilizer (family P) w).subgroupOf (graphLocalGroup (family P) v) =
      normalizer (R : Set (graphLocalGroup (family P) v)) := by
  let A := graphLocalGroup (family P) v
  have he : (normalizer ((R : Subgroup A).map A.subtype : Set G)).subgroupOf A =
      normalizer (R : Set A) := by
    rw [subgroupOf,comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective A.subtype_injective,R.coe_coe]
  rw [←he]
  have hn := source_edge_core_normalizer h hB hw
  rw [←hR] at hn
  ext a
  change (a : G) ∈ stabilizer (family P) w ↔
    (a : G) ∈ normalizer ((R : Subgroup A).map A.subtype : Set G)
  exact ⟨fun ha => (hn.ge ⟨sylowGenerated_le _ a.property,ha⟩).2,
    fun ha => (hn.le ⟨sylowGenerated_le _ a.property,ha⟩).2⟩

/-- Two distinct full edge cores generate the actual local group. -/
theorem graph_intrinsic_two_edgeCores_generate (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z) (hne : w ≠ z) :
    (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ⊔
      (stabilizer (family P) v ⊓ stabilizer (family P) z).pCoreIn 2 =
        graphLocalGroup (family P) v := by
  apply graph_intrinsic_escaping_twoGroup_generates h hB hS hz _
    (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans inf_le_left)
  exact fun hh => hne (graph_intrinsic_edgeCore_unique_neighbor h hB hw hz hh)

/-- An element central in both distinct edge cores is central in the intrinsic actor. -/
theorem graph_intrinsic_edge_omega_inter_le (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z) (hne : w ≠ z) :
    omegaCenterIn ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2) ⊓
      omegaCenterIn ((stabilizer (family P) v ⊓ stabilizer (family P) z).pCoreIn 2) ≤
        omegaCenterIn (graphLocalGroup (family P) v) := by
  intro x hx
  obtain ⟨hxR,hcR,hx2⟩ := (mem_omegaCenterIn_iff _ _).mp hx.1
  obtain ⟨_,hcT,_⟩ := (mem_omegaCenterIn_iff _ _).mp hx.2
  have hgen := graph_intrinsic_two_edgeCores_generate h hB hS hw hz hne
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨hgen ▸ (show x ∈ _ ⊔ _ from mem_sup_left hxR),?_,hx2⟩
  have hh : graphLocalGroup (family P) v ≤ centralizer ({x} : Set G) := by
    rw [←hgen]
    exact sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hcR y hy))
      (fun y hy => mem_centralizer_singleton_iff.mpr (hcT y hy))
  intro y hy
  exact mem_centralizer_singleton_iff.mp (hh hy)

end CFSG.Quasithin.ChapterF.Source.DGS85
