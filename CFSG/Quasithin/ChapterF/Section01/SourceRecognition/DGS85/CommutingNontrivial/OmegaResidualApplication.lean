module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualComparisonApplication

/-!
# Original source application of the residual-omega comparison

The original 6.5(a) obstruction supplies core escape for the selected moving
neighbor. The full edge supplies its actual local Sylow, retaining the
original quotient omega-preimage. Both H and the full omega-displacement
lie in C_Z_lambda(O²(L_alpha')), as required at the start of DGS 8.3.

This does not identify that fixed subgroup with H. The torus restriction,
residual-module dichotomy, paired square estimates and the subsequent
8.4--8.7 conclusions remain with the Chapter 8 assembly.
Source: DGS, Groups and Graphs (1985), 8.3, printed pp.135--136.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Literal original residual-omega setup for 8.3, with moving-neighbor
selection, full-edge Sylow and core escape constructed. -/
theorem reduced_residual_omega_comparison
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
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S₀
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    ∃ w : (graph F).neighborSet a', ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
      ∃ R : Sylow 2 (graphLocalGroup F w.val),
        (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
          (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
        H ≤ Z F w.val ⊓ centralizer
          ((pResidual 2 (graphLocalGroup F a')).map (graphLocalGroup F a').subtype : Set (Reduction.G₀ J S₀)) ∧
        ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
          Z F w.val ⊓ centralizer
            ((pResidual 2 (graphLocalGroup F a')).map (graphLocalGroup F a').subtype : Set (Reduction.G₀ J S₀)) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  have he := CommutingTrivial.core_escape_of_intersection_obstruction F (hob w.val a' w.property.symm)
  have hH := source_critical_displacement_residual_fixed ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w he
  have hHZ := (source_critical_commutator_structure ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models).2.1 w
  exact ⟨w,hm,R,hR,le_inf hHZ (hH.trans inf_le_right),
    source_omega_displacement_residual_fixed ht (Reduction.reduced_borel_core_sylow h)
      d hc hab hd hb hcomm models w hm he R hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
