module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5MovedCubic
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5G2Alignment
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NaturalStarFieldDegree
public import Theory.Representation.G2OrthogonalCover.ParabolicCubicFixed

/-!
# The actual G₂ moved-cover row cannot contain the original A₅ module

The original chosen module supplies a nonzero cubic-fixed vector in the
same core-fixed, fully moved subspace of the classified cover. The literal
normal seed alignment identifies its actor with a root residual over F₄.
The native G₂ calculation makes every such cubic-fixed vector zero.

The full source module stays distinct from the chosen module. This excludes
the specified actual natural moved row, without assuming a block or a
classification of arbitrary binary modules of dimension four.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Exclude the actual natural G₂ moved section from the unchanged original
A₅ source configuration, retaining the full cover and its projection. -/
theorem not_g2_moved_cover_of_a5
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))).subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))))
    (hi : IsIrrPlus ((starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp
      (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))).subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))))
      s.space.toSubmodule)
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)))).subtype)
      (binaryG2 F)) : False := by
  let K := c.K.map c.H.subtype
  let R := c.I.pCoreIn 2
  let C := starImage K R K
  let O := offenderSubgroup (starRepresentation K R)
  have hsource := c.block_source_input hf
  have hCO : C ≤ O := (C27Source.star_moved_section_from_source hsource).1
  let E := (subgroupOfEquivOfLe hCO).symm.trans e.groupEquiv
  let B := (L.subgroupOf K).map (E.toMonoidHom.comp (toStarImage K R))
  have hn : (L.subgroupOf (c.H ⊓ normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer inf_le_right
  have hdeg := C27Source.star_g2_degree_gt_one_from_source hsource F E
  have hlarge : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (show 4 = 2 ^ 2 from rfl).trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hdeg)
  obtain ⟨_,g,hg⟩ := c.c28.constrained_normal_a5_g2_alignment hn d.quotient
    c.K c.component c.quotient c.block_source_outside hf E hlarge
  obtain ⟨A,hA,hm,b,hb,w,hwne,hw,hfix⟩ :=
    a5_source_moved_cubic_fixed_vector d c hf s e.groupEquiv
  exact hwne (Atlas.G2.Natural.OrthogonalCover.ParabolicCubicFixed.cover_moved_subspace_cubic_fixed_eq_zero
    F.Carrier (s.coverProjection e) (by omega) (s.coverProjection_isCover hi e)
    B g hg A hA hm b hb w hw hfix)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
