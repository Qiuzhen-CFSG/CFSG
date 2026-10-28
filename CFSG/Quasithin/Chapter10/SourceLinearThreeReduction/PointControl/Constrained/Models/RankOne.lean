module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Placement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.RankOneSpan

/-!
# Containing-action exclusions for an original rank-one natural cover

The original natural section supplies the full moved span, centralizer
control and Thompson movement, including a positive fixed kernel. The
literal FF action then places the smaller local component inside each
containing model. The moving-scalar obstruction excludes natural SL₃,
repeated natural SL₃, Sp₄ and G₂ actions without supplied span or parabolic
markings. The B.5.1 quotient and the original orbit are unchanged.

The final owner qt-d-10-nona5-point-constrained still constructs the original
and containing action markings and handles the other original source rows.
Source: Aschbacher--Smith 10.2.9, printed pp.751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
  (c : Context D t v I)
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The natural SL₃ containing action is impossible for an original rank-one cover. -/
theorem Context.no_linearThree_source_section_of_rankOne_cover
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s₀ : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    : letI := c.reduced.normal
      letI := c.reduced.elementary
      ∀ (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (_E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  intro s E
  exact c.no_linearThree_source_section_of_local
    (c.actionFacts_of_rankOne_cover n hn hF e s₀) hF hn e
    (c.moved_le_of_rankOne_cover n hn hF e s₀) s E

/-- The natural Sp₄ containing action is impossible for an original rank-one cover. -/
theorem Context.no_symplecticFour_source_section_of_rankOne_cover
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s₀ : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    : letI := c.reduced.normal
      letI := c.reduced.elementary
      ∀ (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (_E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  intro s E
  exact c.no_symplecticFour_source_section_of_local
    (c.actionFacts_of_rankOne_cover n hn hF e s₀) hF hn e
    (c.moved_le_of_rankOne_cover n hn hF e s₀) s E

/-- The natural G₂ containing action is impossible for an original rank-one cover. -/
theorem Context.no_g2_source_section_of_rankOne_cover
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s₀ : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    : letI := c.reduced.normal
      letI := c.reduced.elementary
      ∀ (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (_E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (Atlas.G2.Natural.action F))), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  intro s E
  exact c.no_g2_source_section_of_local
    (c.actionFacts_of_rankOne_cover n hn hF e s₀) hF hn e
    (c.moved_le_of_rankOne_cover n hn hF e s₀) s E

/-- Every repeated natural SL₃ containing action is impossible for an original rank-one cover. -/
theorem Context.no_repeatedThree_source_section_of_rankOne_cover
    {n r : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (s₀ : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    : letI := c.reduced.normal
      letI := c.reduced.elementary
      ∀ (s : MovedSection (action (internalModule D v I))
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))))
    (_E : ActionEquiv (s.space.toRepresentation.comp
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subtype)
      (repeated (Representation.restrictScalars (k := ZMod 2)
        (specialLinearNatural (k := F) 3)) r)), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  intro s E
  exact c.no_repeatedThree_source_section_of_local
    (c.actionFacts_of_rankOne_cover n hn hF e s₀) hF hn e
    (c.moved_le_of_rankOne_cover n hn hF e s₀) s E

end CFSG.Quasithin.Chapter10.PointControl.Constrained
