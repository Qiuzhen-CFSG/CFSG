module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveMixedCriticalData
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableA5CriticalOrientation

/-!
# The literal directed critical base edge in the wreath-five configuration

The marked A₅ endpoint is the first vertex of a critical pair. Translating
that directed pair gives criticality of the actual base edge from type true
to type false. All original source markings and the first Borel are retained.
This supplies the directed edge needed by the small-beta exclusions.
Source: Aschbacher--Smith 15.2.4--8, printed pp.1106--1110;
DGS, *Groups and Graphs* (1985), (11.4)--(11.5), pp.171--172.
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

/-- The original wreath-five assumption supplies the literal A₅-to-small
critical base edge. Criticality is transported, never reversed. -/
theorem ChosenSmallSource.HStar_wreath_five_canonical_critical_edge
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
      b F = 1 ∧ IsCriticalPair F (base F true) (base F false) ∧
        ⁅Z F (base F true),Z F (base F false)⁆ = ⊥ := by
  obtain ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,hb⟩ :=
    h.HStar_wreath_five_distance_one_mixed_pair hH he
  let := hA
  let := hfin
  exact ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,hb,
    Assembly.small_solvable_a5_base_critical hF hq ha hb⟩

end CFSG.Quasithin.Chapter15.Section02
