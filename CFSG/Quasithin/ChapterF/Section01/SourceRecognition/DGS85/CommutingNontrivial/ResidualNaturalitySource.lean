module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualNaturalityExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceSource

/-!
# Original-source natural residual exclusion

Under the original F1.11 hypotheses and the full local model catalogue,
the nonzero terminal intersection commutator forces critical distance
three. The source 6.5 theorem supplies the adjacent-core obstruction.
The all-field exclusion therefore rules out a natural beta residual
section without either of these as an additional premise.

Source: DGS, *Groups and Graphs* (1985), 6.5 and 8.5,
printed pp.121--122 and 139.
-/

@[expose] public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The natural residual section is excluded from the original source
hypotheses and full local catalogue, for every positive field degree. -/
theorem reduced_natural_residual_exclusion_of_catalogue
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
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,F)) :
    ¬ NaturalResidualSection h beta e n := by
  intro hres
  exact reduced_natural_residual_exclusion h (Reduction.reduced_graph_core_obstruction h)
    models hc hab hd (reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne)
    hcomm hne hn hF e hres

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
