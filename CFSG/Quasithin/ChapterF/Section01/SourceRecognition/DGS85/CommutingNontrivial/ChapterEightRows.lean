module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReducedModuleEstimates

/-!
# Reduced 8.3 row interface

This module exposes the already proved model row estimates under a single
Chapter-8 entry point.  It deliberately keeps the original reduced graph,
quotient and moving-neighbor witness; no model classification is hidden here.
The Suzuki row is the first 8.3--8.7 consumer used by source assembly.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type*} [Group G]

/-- The reduced Suzuki row of DGS 8.3, retaining the literal moving neighbor
and its nonzero intersection.  This is an assembly alias for the proved
`reduced_moving_suzuki_index_bound`; the model parameter `m` is unconstrained
so the field-two Suzuki case remains available to later catalogue consumers.
-/
theorem reduced_chapterEight_suzuki_row
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (m : ℕ) :
    let F := Reduction.reducedFamily J S₀
    let A := V F beta 1 ⊓ Q F a'
    ∃ w : (graph F).neighborSet a',
      ⁅A, Z F w.val⁆ ≠ ⊥ ∧
      ∀ _e : (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≃* SuzukiMatrixGroup m,
        (Q F w.val).relIndex A ^ 2 ≤
          (centralizer (A : Set (Reduction.G₀ J S₀))).relIndex (Z F w.val) := by
  exact reduced_moving_suzuki_index_bound h hob hc hab hd hb hcomm hne m

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
