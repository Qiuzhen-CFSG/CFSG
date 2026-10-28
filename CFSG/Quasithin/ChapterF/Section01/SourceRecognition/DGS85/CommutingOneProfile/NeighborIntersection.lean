module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphSeeds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity

/-!
# The neighboring-core intersection in Chapter 11

Let I be the intersection of Qδ over every neighbor of beta, as at the
start of (11.6). The full beta stabilizer normalizes I, which lies in Qβ.
The unrestricted beta-span of Zα centralizes I. Critical escape makes that
normal span non-two-closed, so source (6.2)(b) proves that C_Gβ(I) is
transitive on the neighbors.

This establishes the opening centralizer-transitivity assertion of (11.6)
with no local-generation or action hypothesis beyond the genuine source
triple and its two-closed Borel. It does not yet identify I with Zβ or
prove its intersections two steps farther away trivial. The unrestricted
center span used here remains distinct from the corrected Chapter 11 Vβ.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.6), printed p.172, using (6.2)(b), printed p.119.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The intersection at the start of (11.6), over every actual neighbor. -/
def neighborCoreIntersection (F : Bool → Subgroup G) (b : Vertex F) : Subgroup G :=
  ⨅ c : (graph F).neighborSet b, Q F c.val

theorem neighborCoreIntersection_le (F : Bool → Subgroup G) {a b : Vertex F}
    (hab : (graph F).Adj a b) : neighborCoreIntersection F b ≤ Q F a :=
  iInf_le (fun c : (graph F).neighborSet b => Q F c.val) ⟨a,hab.symm⟩

/-- The whole vertex stabilizer normalizes the intersection of its neighboring cores. -/
theorem neighborCoreIntersection_normalized (F : Bool → Subgroup G) (b : Vertex F) :
    stabilizer F b ≤ normalizer (neighborCoreIntersection F b : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  apply mem_iInf.mpr
  intro c
  have hgc : (graph F).Adj b (g⁻¹ • c.val) := by
    have he := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr c.property
    change (graph F).Adj (g⁻¹ • b) (g⁻¹ • c.val) at he
    rwa [show g⁻¹ • b = b from (stabilizer F b).inv_mem hg] at he
  have hxq : x ∈ Q F (g⁻¹ • c.val) := mem_iInf.mp hx ⟨g⁻¹ • c.val,hgc⟩
  have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hxq
  rw [←Q_translate,smul_inv_smul] at hm
  exact hm

/-- This neighboring intersection lies in the actual beta core, not just in Uβ. -/
theorem source_neighborCoreIntersection_le_core (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    neighborCoreIntersection (family P) b ≤ Q (family P) b := by
  have ha := neighborCoreIntersection_le (family P) hab
  have hWb : neighborCoreIntersection (family P) b ≤ stabilizer (family P) b :=
    ha.trans ((source_Z_Q_U h a).2.trans
      ((ballKernel_one_le_edge _ hab).trans inf_le_right))
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le ha) hWb
    (neighborCoreIntersection_normalized _ b)

/-- The unrestricted neighboring center span centralizes the core intersection.
It is distinct from Chapter 11's corrected Vβ. -/
theorem source_neighbor_center_span_centralizes_intersection
    (h : LocallyRankOneTriple P B) {a b : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) :
    conjugateSpanBy (Z (family P) a) (stabilizer (family P) b) ≤
      centralizer (neighborCoreIntersection (family P) b : Set G) := by
  let := finite_endpoints h
  apply (closure_le _).mpr
  rintro z ⟨g,hg,x,hx,rfl⟩
  have hbg : (graph (family P)).Adj b (g • a) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab.symm
    change (graph (family P)).Adj (g • b) (g • a) at hh
    rwa [show g • b = b from hg] at hh
  have hxg : g * x * g⁻¹ ∈ Z (family P) (g • a) := by
    rw [Z_translate]
    exact mem_map_of_mem _ hx
  exact (le_centralizer_iff.mp (source_core_centralizes_center h (g • a)) |>.trans
    (centralizer_le (neighborCoreIntersection_le (family P) hbg.symm))) hxg

/-- A critical center makes its unrestricted beta-normal closure non-two-closed. -/
theorem source_critical_center_span_not_twoClosed
    (h : LocallyRankOneTriple P B) {a b : Vertex (family P)}
    (hc : IsCriticalPair (family P) a b) (hb : DGS85.b (family P) = 1) :
    let R := conjugateSpanBy (Z (family P) a) (stabilizer (family P) b)
    ¬ ∃ T : Sylow 2 R, (T : Subgroup R) = pCore 2 R := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let R := conjugateSpanBy (Z (family P) a) (stabilizer (family P) b)
  have hab := source_critical_one_adjacent hc hb
  have hZa : Z (family P) a ≤ stabilizer (family P) b :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right))
  have hRb : R ≤ stabilizer (family P) b := conjugateSpanBy_le_self hZa
  let : Finite R := Finite.of_injective (inclusion hRb) (inclusion_injective _)
  change ¬ ∃ T : Sylow 2 R, (T : Subgroup R) = pCore 2 R
  intro hs
  have hZQ : Z (family P) a ≤ R.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow R _ (le_conjugateSpanBy _ _)
      (IsElementaryAbelian.isPGroup 2 _) hs
  have hRcore : R.pCoreIn 2 ≤ Q (family P) b :=
    pCoreIn_mono_of_normalizes hRb (le_normalizer_conjugateSpanBy _ _)
  exact hc.2 ((hZQ.trans hRcore).trans (source_Z_Q_U h b).2)

/-- The actual beta centralizer of the neighboring-core intersection is
transitive. This is the first transitivity assertion used in (11.6). -/
theorem source_neighbor_core_centralizer_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    {c : Vertex (family P)} (hbc : (graph (family P)).Adj b c) :
    ∃ g ∈ stabilizer (family P) b ⊓ centralizer
      (neighborCoreIntersection (family P) b : Set G), g • a = c := by
  let R := conjugateSpanBy (Z (family P) a) (stabilizer (family P) b)
  have hab := source_critical_one_adjacent hc hb
  have hZa : Z (family P) a ≤ stabilizer (family P) b :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right))
  have hRb : R ≤ stabilizer (family P) b := conjugateSpanBy_le_self hZa
  obtain ⟨g,hg,he⟩ := source_nonclosed_normal_transitive h hB hab.symm R hRb
    (le_normalizer_conjugateSpanBy _ _) (source_critical_center_span_not_twoClosed h hc hb) c hbc
  exact ⟨g,⟨hRb hg,source_neighbor_center_span_centralizes_intersection h hab hg⟩,he⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
