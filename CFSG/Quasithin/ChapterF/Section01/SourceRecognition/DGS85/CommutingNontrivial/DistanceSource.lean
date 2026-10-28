module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceApplications
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PredecessorNormality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# Original F1.11 distance and predecessor applications

The original-source 6.5 theorem supplies the adjacent-core obstruction in
the distance-three proof and the uniform Chapter 9 distance premise. The
actual local rank-one catalogue remains explicit; its exceptional order-144
enlargement is not inferred from the distance proof.

Independently, the same original earlier-local construction supplies the
predecessor image theorem at b = 3 without any model catalogue. An order-two
neighboring-span image in a terminal SD16 image is central there. This does
not establish b = 3 or the SD16 marking in the exceptional enlargement.

Source: DGS, *Groups and Graphs* (1985), 6.5, 8.1(g) and 8.4,
pp.121--122,133,137--138.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original source proves the 6.5 premise; only the local catalogue remains. -/
theorem reduced_distance_three_of_catalogue
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    : b (Reduction.reducedFamily J S₀) = 3 :=
  reduced_distance_three h (Reduction.reduced_graph_core_obstruction h) models hc hab hd hb hcomm hne

/-- Chapter 9's distance premise with the original 6.5 input discharged. -/
theorem reduced_chapter_eight_distance_of_catalogue
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    : CommutingTrivial.ChapterEightDistance (Reduction.reducedFamily J S₀) :=
  reduced_chapter_eight_distance h (Reduction.reduced_graph_core_obstruction h) models

/-- The order-two terminal image is central in a marked SD16 image at b = 3,
using the original F1.11 earlier-local data and no endpoint catalogue. -/
theorem reduced_distance_three_predecessor_image_centrality
    (h : HypothesisF11 J S₀)
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)} (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : b (Reduction.reducedFamily J S₀) = 3) (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥) :
    ∃ prev : Vertex (Reduction.reducedFamily J S₀), (graph (Reduction.reducedFamily J S₀)).Adj a' prev ∧
      (graph (Reduction.reducedFamily J S₀)).Adj beta prev ∧
      V (Reduction.reducedFamily J S₀) beta 1 ≤ Q (Reduction.reducedFamily J S₀) prev ∧
      Q (Reduction.reducedFamily J S₀) prev ≤ normalizer (V (Reduction.reducedFamily J S₀) beta 1 : Set (Reduction.G₀ J S₀)) ∧
      ∃ R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a'),
        (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) a')).map (graphLocalGroup (Reduction.reducedFamily J S₀) a').subtype =
          (stabilizer (Reduction.reducedFamily J S₀) a' ⊓ stabilizer (Reduction.reducedFamily J S₀) prev).pCoreIn 2 ∧
        let L := graphLocalGroup (Reduction.reducedFamily J S₀) a'
        let q := QuotientGroup.mk' (pCore 2 L)
        let E := ((V (Reduction.reducedFamily J S₀) beta 1).subgroupOf L).map q
        let A := ((Q (Reduction.reducedFamily J S₀) prev).subgroupOf L).map q
        let S := (R : Subgroup L).map q
        E ≤ A ∧ A ≤ S ∧
          ∀ s t : S, orderOf s = 8 → orderOf t = 2 → t*s*t⁻¹ = s^3 →
            closure ({s,t} : Set S) = ⊤ → Nat.card E = 2 →
            E ≤ centralizer (S : Set (L ⧸ pCore 2 L)) := by
  exact source_distance_three_predecessor_image_centrality (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedFullEarlierLocalTheorems h)
    hc hab hd hb hcomm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
