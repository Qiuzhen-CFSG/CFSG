module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveMixedDistanceOne
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourMarkings

/-!
# Canonical critical data for the original wreath-five pair

The literal faithful completion has a directed commuting critical edge and
the complete earlier-local rank-one catalogue, both intrinsically and after
the actual inclusion into the original completion. The edge is not reversed
to prescribe its first endpoint. Both original quotient markings, the common
Sylow and the first Borel remain part of the data.

This discharges the catalogue and critical-edge existence inputs of the
distance-one local exclusions. It does not assert their remaining path or
orientation arguments.
Source: Aschbacher--Smith 15.2.4--8, printed pp.1106--1110;
DGS, *Groups and Graphs* (1985), reduction pp.95--96 and Chapter 11.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual wreath-five completion supplies its full local catalogue and
a directed commuting critical pair. No endpoint orientation is imposed. -/
theorem ChosenSmallSource.HStar_wreath_five_mixed_critical_data
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A)
      (L : Fin 2 → Subgroup A) (S : Subgroup A),
      IsQuasithin A ∧ HypothesisF11 L S ∧
      S ⊔ borel (L 0) S = S ∧
      (Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
        Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)) ∧
      let F := Reduction.reducedFamily L S
      b F = 1 ∧
      (∀ v : Vertex F, IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v))) ∧
      (∀ v : Vertex F,
        IsRankOneModel ((graphLocalGroup F v).map (Reduction.G₀ L S).subtype ⧸
          pCore 2 ((graphLocalGroup F v).map (Reduction.G₀ L S).subtype))) ∧
      ∃ a beta : Vertex F, IsCriticalPair F a beta ∧
        (graph F).Adj a beta ∧ ⁅Z F a,Z F beta⁆ = ⊥ := by
  obtain ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,hb⟩ :=
    h.HStar_wreath_five_distance_one_mixed_pair hH he
  let := hA
  let := hfin
  refine ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,hb,
    Assembly.small_solvable_a5_graph_models hF hq ha,
    Assembly.small_solvable_a5_original_graph_models hF hq ha,?_⟩
  obtain ⟨a,beta,hc⟩ := source_exists_criticalPair (Reduction.reduced_triple hF)
  exact ⟨a,beta,hc,SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb),
    Reduction.reduced_critical_commuting_of_small_solvable hF false hq hc⟩

end CFSG.Quasithin.Chapter15.Section02
