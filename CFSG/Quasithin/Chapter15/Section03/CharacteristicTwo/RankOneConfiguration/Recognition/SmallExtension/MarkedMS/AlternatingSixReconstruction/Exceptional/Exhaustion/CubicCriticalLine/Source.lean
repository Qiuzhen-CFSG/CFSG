module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicCriticalLine.Movement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicCriticalLine

/-!
# Applications of the cubic critical-line reduction

At distance two, a cubic initial kernel forces every critical image to be
one transposition. A different critical-image order is therefore excluded.
Quadraticity of the opposite Q-image supplies whole-core exhaustion by the
literal graph argument, so all exceptional core clauses and the original
rank-two conclusion follow. The critical commutator is now an actual order-two line disjoint from the
component-fixed attachment, and equals the commutator of the full X-layers.
The literal source-line bound feeds both the whole-core and rank-two
conclusions below. Its remaining orbit proof and larger critical distances
remain obligations of this reconstruction owner.

Source: MS93 (3.3)(ii), (3.6), pp.866--871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "T" => edge L R

open ChapterC in
/-- The quadratic-image test yields all clauses for the entire original
blockU through the actual exhaustion equality. -/
theorem core_facts_of_distanceTwo_cubic_quadratic
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hq : IsQuadratic (BinaryPermutation.coreRepresentation (Fin 6))
      (CubicAction.graphImage h e hz hk (Q T c))) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_opposite_quadratic_image h e hz hk hb c hc hq)

/-- The original C.1.32 consumer of the cubic quadratic-image branch. -/
theorem rankTwo_of_distanceTwo_cubic_quadratic
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hq : IsQuadratic (BinaryPermutation.coreRepresentation (Fin 6))
      (CubicAction.graphImage h e hz hk (Q T c))) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_opposite_quadratic_image h e hz hk hb c hc hq)

/-- A non-line critical image is excluded in the original rank-two consumer,
including the formerly remaining critical four-images. -/
theorem rankTwo_of_distanceTwo_cubic_nonLine
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hn : Nat.card (CubicAction.graphImage h e hz hk (X T c)) ≠ 2) :
    RankTwoAlternatives L R :=
  (hn (CubicAction.critical_image_card_two h e hz hk hb c hc)).elim

include h e hz hk in
/-- The literal source Z-index can be used directly in the unchanged
C.1.32 consumer; every larger-image cubic branch is excluded. -/
theorem rankTwo_of_distanceTwo_cubic_source_index_ne_two
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hn : (Q T (alpha T)).relIndex (Z T c) ≠ 2) : RankTwoAlternatives L R :=
  (hn (CubicAction.critical_Z_core_index_two h e hz hk hb c hc)).elim


include h e hz hk in
/-- The source bound with its actual order-two critical line exhausts the
whole intrinsic core. The remaining orbit argument must supply this bound;
this conditional application does not assert the full source theorem. -/
theorem rankTwo_of_distanceTwo_cubic_source_line_bound
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hbound : ⁅Q T (alpha T),Z T c⁆ ≤
      ⁅Q T (alpha T),X T c ⊓ Q T (alpha T)⁆ ⊔ ⁅Z T (alpha T),Z T c⁆) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_critical_line_bound h e hz hk hb c hc hbound)

include h e hz hk in
open ChapterC in
/-- The same literal source-line bound gives every exceptional clause for
blockU, including its full centralizer rather than a constituent centralizer. -/
theorem core_facts_of_distanceTwo_cubic_source_line_bound
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hbound : ⁅Q T (alpha T),Z T c⁆ ≤
      ⁅Q T (alpha T),X T c ⊓ Q T (alpha T)⁆ ⊔ ⁅Z T (alpha T),Z T c⁆) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_critical_line_bound h e hz hk hb c hc hbound)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
