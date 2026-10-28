module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeChief
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorQuadraticRatio

/-!
# Chief-factor selection from the original tensor hypotheses

The binary tensor model supplies both the four-thirds quadratic bound and
the exclusion of dual FF. Applying the source chief-factor selection now
produces a noncentral factor of the actual H-conjugate span with quadratic
ratio at most two, using only the original PSL₃(4) branch hypotheses.
The representation-theoretic exclusion of that factor is a separate step.

Source: Aschbacher--Smith9.2.7 and3.1.6, printed pp.731--732 and573--575.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB ChapterD ChapterD.UniqueFactor ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original PSL₃(4) alternative supplies an actual small-ratio noncentral chief factor. -/
theorem old_residual_linear_three_exists_small_chief_of_tensor
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceImage
        (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    :
    let U := (conjugateSpan H D.fullModule).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U, letI := hU
      ∃ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i ∧
        quadraticRatio (Representation.BinaryOffender.imageRepresentation
          (s.factorRepresentation i)) ≤ 2 :=
  m.old_residual_linear_three_exists_small_chief hH hlarge hK hm
    m.source_fullModule_quadraticRatio_four_thirds m.source_fullModule_dual_notFF

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
