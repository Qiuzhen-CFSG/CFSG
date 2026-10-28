module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualRoot
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualComparisonApplication

/-!
# Residual-intersection control on the original reduced source

The original 6.5(a) obstruction supplies the adjacent-core escape. The
counterexample calculation then puts the marked residual intersection in
the original quotient omega-preimage and its displacement in the literal
residual fixed denominator. Both full-edge and quotient maps are retained,
for arbitrary critical orientation. Naturality exclusion and the paired
square estimates remain Chapter 8 obligations.
Source: DGS, Groups and Graphs (1985), proof of 8.3, printed pp.135–136.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original counterexample branch of 8.3 supplies a proper residual
intersection whose image is in the moving omega-center. Its displacement
is killed by the actual residual-section denominator. All quotients and
edge markings are those of the reduced F1.11 graph. -/
theorem reduced_counterexample_residual_edge_control
    (h : HypothesisF11 J S₀)
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
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆) :
    let F := Reduction.reducedFamily J S₀
    let T := (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype
    let E := (pResidual 2 (graphLocalGroup F a')).map (graphLocalGroup F a').subtype
    let T₀ := T ⊓ (E ⊔ Q F w.val)
    T₀ < T ∧ T₀ ≤ quotientSylowOmegaPreimage (graphLocalGroup F w.val) R ∧
      ⁅T₀,Z F w.val⁆ ≤ Z F w.val ⊓ centralizer (E : Set (Reduction.G₀ J S₀)) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have he := CommutingTrivial.core_escape_of_intersection_obstruction F (hob w.val a' w.property.symm)
  have hproper := source_counterexample_residual_edge_proper ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm he R hR hbad
  have hle := source_counterexample_residual_edge_le_omega ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm he R hR hbad
  have hdisp := source_omega_displacement_residual_fixed ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm he R hR
  exact ⟨lt_of_le_not_ge inf_le_left (fun hh => hproper (hh.trans inf_le_right)),hle,
    (commutator_mono hle le_rfl).trans hdisp⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
