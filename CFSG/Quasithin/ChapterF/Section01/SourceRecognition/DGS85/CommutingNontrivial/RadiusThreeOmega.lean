module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientOmegaAction

/-!
# The first marked omega placement in DGS 8.4(3)

A radius span inside a local Sylow maps into its quotient omega-center:
each original center generator is elementary, so its image has exponent
two and is central in that same quotient Sylow. Taking their join proves
the statement without asserting that the entire original span is elementary.

The complete 8.4(1) containment places W in the full predecessor edge core.
Its actual Sylow at the critical endpoint then gives W <= A with precisely
the original two-core quotient map. The final theorem applies this to the
literal reduced F1.11 graph at every ordered critical pair.

Source: DGS, *Groups and Graphs* (1985), 8.4(1,3), printed pp.137--138.
The separate W intersect Q_alpha' placement at the moving neighbor, the
residual argument, b=3 and 8.5--8.7 are not conclusions of this module.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A center span lying in an actual local Sylow maps into its full
quotient omega-center. Only the individual center generators are elementary;
no exponent assumption on the whole span is required. -/
theorem source_span_le_quotient_omega (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v beta : Vertex (family P)) (r : ℕ)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup v))
    (hV : V (family P) beta r ≤ (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype) :
    V (family P) beta r ≤ quotientSylowOmegaPreimage (d.localGroup v) R := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hZV : Z F x ≤ V (family P) beta r := le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have hZS : Z F x ≤ (R : Subgroup L).map L.subtype := hZV.trans hV
  have hZL : Z F x ≤ L := hZS.trans (map_subtype_le _)
  let := CommutingOneProfile.source_center_elementary h x
  let : IsElementaryAbelian 2 ((Z F x).subgroupOf L) := IsElementaryAbelian.subgroupOf hZL
  let : IsElementaryAbelian 2 (((Z F x).subgroupOf L).map q) := IsElementaryAbelian.map q
  have hsub : (Z F x).subgroupOf L ≤ (R : Subgroup L) := by
    intro z hz
    obtain ⟨t,ht,he⟩ := hZS hz
    exact (Subtype.ext he : t = z) ▸ ht
  have homega := source_rank_one_elementary_le_sylow_omega M
    (R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L)))
    (((Z F x).subgroupOf L).map q) (map_mono hsub)
  intro z hz
  exact ⟨⟨z,hZL hz⟩,homega (mem_map_of_mem q hz),rfl⟩

/-- The first marked omega placement in 8.4(3), together with full 8.4(1).
The Sylow belongs to the literal endpoint local group and maps to the full
edge core. The separate intersection placement at the moving neighbor is
not asserted here. -/
theorem source_radius_three_omega (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 3 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥) :
    ∃ (prev : Vertex (family P)) (R : Sylow 2 (d.localGroup a')),
      (graph (family P)).Adj a' prev ∧
      (graph (family P)).dist beta prev + 1 = (graph (family P)).dist beta a' ∧
      V (family P) beta 3 ≤ Q (family P) prev ∧
      (R : Subgroup (d.localGroup a')).map (d.localGroup a').subtype =
        (stabilizer (family P) a' ⊓ stabilizer (family P) prev).pCoreIn 2 ∧
      V (family P) beta 3 ≤ quotientSylowOmegaPreimage (d.localGroup a') R := by
  obtain ⟨prev,hprev,hdprev,hW⟩ := source_radius_three_core h hB d hob models hc hab hd hb hcomm hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hprev
  refine ⟨prev,R,hprev,hdprev,hW,hR,source_span_le_quotient_omega h d a' beta 3 (models a') R ?_⟩
  rw [hR,inf_comm]
  exact hW.trans (Noncommuting.graph_Q_le_edgeCore h hprev.symm)

/-- Literal reduced-F1.11 application, for every ordered nontrivial commuting
critical pair. All original quotient, center and full-edge markings survive. -/
theorem reduced_radius_three_omega
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S₀
    ∃ (prev : Vertex F) (R : Sylow 2 (graphLocalGroup F a')),
      (graph F).Adj a' prev ∧
      (graph F).dist beta prev + 1 = (graph F).dist beta a' ∧
      V F beta 3 ≤ Q F prev ∧
      (R : Subgroup (graphLocalGroup F a')).map (graphLocalGroup F a').subtype =
        (stabilizer F a' ⊓ stabilizer F prev).pCoreIn 2 ∧
      V F beta 3 ≤ quotientSylowOmegaPreimage (graphLocalGroup F a') R :=
  source_radius_three_omega (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hob models hc hab hd hb hcomm hne


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
