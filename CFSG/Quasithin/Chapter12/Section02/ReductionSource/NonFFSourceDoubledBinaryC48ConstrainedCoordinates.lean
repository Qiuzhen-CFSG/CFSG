module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedExterior
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition

/-!
# Marked exterior coordinates for the original constrained source

The actual irreducible ten-dimensional section is identified with the exterior
square. Its original end-node offender marking is retained, and the coordinate
actor is exactly that marking or its inverse-transpose graph twist. The same
original six-space embedding, central quotient and full source conclusion
remain present.
Source: Aschbacher--Smith B.5.1, I.1.6(7), C.4.8 and 12.1.11.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

open Representation.SL5ExteriorSquare Representation.SL5TenDimensional

/-- Actual exterior coordinates with the original end-node marking preserved. -/
@[expose] def ConstrainedExteriorCoordinates
    {E Y : Type*} [_root_.Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) : Prop :=
  ∃ (mark actor : C ≃* SL(5,ZMod 2))
    (coordinates : s.space.toSubmodule ≃ₗ[ZMod 2] ExteriorModule 2),
    (∀ A, IsBestOffender s.action A → IsEndNodeRadical ((A.subgroupOf C).map mark.toMonoidHom)) ∧
    (actor = mark ∨ actor = mark.trans Duality.graph) ∧
    ∀ g v, coordinates (s.space.toRepresentation.comp C.subtype g v) =
      exteriorAction 2 (actor g) (coordinates v)

private theorem exterior_coordinates
    {E Y : Type*} [_root_.Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) (hs : ConstrainedExteriorSection s) :
    ConstrainedExteriorCoordinates s := by
  obtain ⟨_,_,_,_,mark,ho,_,hir,hd⟩ := hs
  let : IsIrreducible (s.space.toRepresentation.comp C.subtype) := hir
  obtain ⟨actor,coordinates,hactor,he⟩ := square_coordinates_of_finrank_ten
    (s.space.toRepresentation.comp C.subtype) mark hd
  exact ⟨mark,actor,coordinates,ho,hactor,he⟩

universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Original source hypotheses supply coordinates on the same classified
section and original embedding, with the exact graph-twist alternative. -/
theorem sourceOrbit_binary_witness_constrained_exterior_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let ρ := starRepresentation (K.map H.subtype) (J.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ∃ _hCO : C ≤ O,
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp O.subtype) (C.subgroupOf O),
      ∃ i : Additive D.sourceOrbit →ₗ[ZMod 2] c.sectionData.space.toSubmodule,
        (∀ v, (((i v).val.toMul : ((K.map H.subtype) ⊔ (J.pCoreIn 2) : Subgroup G)) : G) = v.toMul) ∧
        SixSpaceMovedEmbedding c.sectionData
          ((starImage (K.map H.subtype) (J.pCoreIn 2) (J.pCoreIn 2)).subgroupOf O) i ∧
        ConstrainedExteriorSection c.sectionData ∧
        ConstrainedExteriorCoordinates c.sectionData := by
  obtain ⟨hCO,c,i,hi,hdata,hs⟩ := D.sourceOrbit_binary_witness_constrained_exterior
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  exact ⟨hCO,c,i,hi,hdata,hs,exterior_coordinates c.sectionData hs⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
