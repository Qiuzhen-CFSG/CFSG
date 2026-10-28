module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Quintic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveMixedPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSolvableCriticalCommuting

/-!
# The commuting reduction for the actual marked-five source pairs

The original marked-five S₃ pair has its literal residual first factor,
common Sylow subgroup and D₁₀/Sz(2) quotient. The faithful mixed pair from
a wreath quotient has the same small-solvable marking and an A₅ opposite
endpoint, even after taking the necessary two-core quotient. Applying the
DGS noncommuting exclusion shows that every critical pair in either
reduced graph is commuting, with all source markings retained.

This discharges only the noncommuting branch of the required recognition.
The commuting branch and final H-star recognition remain genuine inputs.
Source: Aschbacher--Smith 15.2.4--8, printed pp.1106--1110, and F.1.12,
printed pp.262--264; DGS, *Groups and Graphs* (1985), Chapters 7--11.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every critical pair in the literal marked-five S₃ reduced graph is commuting. -/
theorem ChosenSmallSource.marked_five_symmetricThree_critical_commuting
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let F := Reduction.reducedFamily ![h.residual ⊔ (M ⊓ Mc).pCoreIn 2,H] (T : Subgroup G)
    ∀ v w : Vertex F, IsCriticalPair F v w → ⁅Z F v,Z F w⁆ = ⊥ := by
  obtain ⟨hF,hq,_⟩ := h.marked_five_symmetricThree_recognition_data hd hH he
  dsimp only
  intro v w hc
  exact Reduction.reduced_critical_commuting_of_small_solvable hF false hq hc

/-- The faithful wreath mixed pair retains quasithinness, both quotient markings
and the full first-Borel condition, and every critical pair is commuting. -/
theorem ChosenSmallSource.HStar_wreath_five_commuting_mixed_pair
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
      ∀ v w : Vertex F, IsCriticalPair F v w → ⁅Z F v,Z F w⁆ = ⊥ := by
  let := h.prepared.elementary
  obtain ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha⟩ :=
    source_HStar_wreath_five_faithful_mixed_pair h.ambient T h.empty h.maximal
      h.centralizing h.partner h.many h.prepared h.small hH he
  let := hA
  let := hfin
  refine ⟨A,hA,hfin,L,S,hqt,hF,hB,hq,ha,?_⟩
  dsimp only
  intro v w hc
  exact Reduction.reduced_critical_commuting_of_small_solvable hF false hq hc

end CFSG.Quasithin.Chapter15.Section02
