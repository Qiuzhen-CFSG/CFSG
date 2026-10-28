module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Edges
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The actual line residual in the natural U coordinates

Absorb the marking of U into the quotient projection before choosing a line
parabolic. This keeps the natural and contragredient actions in the same
coordinates. The residual is the source-ordered O²(O^{2′}(P)); its equality
with the embedded O²(P) uses the two-group kernel, not an identification of
the residual with the whole parabolic.

These definitions do not assert that the residual normalizes a moving
commutator. That assertion is the representation argument in MS93 (4.3.2)(3),
printed p.884, following the opposite-orientation conclusion in step (2).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M} {a : Vertex R}

/-- The quotient projection expressed in the given natural U coordinates. -/
def naturalProjection (o : MovingOrientationAt a) : stabilizer R a →* SL :=
  o.naturalU.marking.toMonoidHom.comp o.projection

theorem naturalProjection_surjective (o : MovingOrientationAt a) :
    Function.Surjective (naturalProjection o) :=
  o.naturalU.marking.surjective.comp o.natural_section.projection_surjective

theorem naturalProjection_kernel (o : MovingOrientationAt a) :
    (naturalProjection o).ker = (Q R a).subgroupOf (stabilizer R a) := by
  rw [naturalProjection, MonoidHom.ker_comp_of_injective _ _ o.naturalU.marking.injective]
  exact o.natural_section.projection_kernel

/-- A line parabolic for the action on U, inside the finite vertex stabilizer. -/
def lineParabolic (o : MovingOrientationAt a) (flag : SL) :
    Subgroup (stabilizer R a) := parabolic (naturalProjection o) flag true

/-- The actual ordered rank-one residual of this parabolic. -/
def lineResidual (o : MovingOrientationAt a) (flag : SL) :
    Subgroup (stabilizer R a) := rankOne (lineParabolic o flag)

variable [Finite M]

theorem lineResidual_eq (source : LocalSource L R) (ha : color R a = false)
    (o : MovingOrientationAt a) (flag : SL) :
    lineResidual o flag =
      (pResidual 2 (lineParabolic o flag)).map (lineParabolic o flag).subtype := by
  let := finite_stabilizer R a
  apply rankOne_parabolic_eq _ (naturalProjection_surjective o)
  rw [naturalProjection_kernel]
  exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype

theorem lineResidual_isPPerfect (source : LocalSource L R) (ha : color R a = false)
    (o : MovingOrientationAt a) (flag : SL) : IsPPerfect 2 (lineResidual o flag) := by
  let := finite_stabilizer R a
  rw [lineResidual_eq source ha]
  exact isPPerfect_embedded_pResidual 2 _

theorem lineResidual_le_localResidual (source : LocalSource L R)
    (ha : color R a = false) (o : MovingOrientationAt a) (flag : SL) :
    lineResidual o flag ≤ pResidual 2 (stabilizer R a) := by
  let := finite_stabilizer R a
  exact le_pResidual_of_isPPerfect _ (lineResidual_isPPerfect source ha o flag)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne
