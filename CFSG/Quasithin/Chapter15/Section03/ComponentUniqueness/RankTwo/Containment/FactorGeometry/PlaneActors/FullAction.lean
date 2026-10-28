module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.CoordinateData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Lifting
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Coordinates

/-!
# The residual plane actors when Y₊ = Y

The genuine 15.3.7 image and the order-nine two-core quotient identify the
actual action kernel. The proved cubic coordinate calculation gives both
residual-centralizer images order three and identifies their moving planes.
Lifting through the two-group kernel gives both three-parts, and
two-perfectness gives generation of Y. Relative normality inside Y and
stabilizer invariance follow from the plane geometry. The right actor is
exactly O²(C_Y(V₁)).

The final construction discharges the coordinate premise of the assembly
helper. Its only local-action inputs are the compatible natural action,
the full residual image, and the order-nine two-core quotient. It makes
neither of the source containment assertions in 15.3.39–40.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7,
15.3.10(1), and 15.3.39–40, printed pp.1122–1123 and 1137–1138.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- Assemble CaseOne after the actual cubic coordinate calculation has been proved.
The additional coordinate premise must be discharged by its producer. -/
theorem planeActorPair_of_fullActionCoordinates {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (_hVM : V ≤ M)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9)
    (hc : FullActionCoordinateFacts d (residualY M Mc)) :
    ∃ a : PlaneActorPair M (residualY M Mc) (residualY M Mc)
      (planeStabilizer T (d.plane 1)) V (d.plane 1)
      (d.plane (Multiplicative.ofAdd (1 : ZMod 2))),
      a.right = centralizingFactor (residualY M Mc) (d.plane 1) := by
  let j : OrthogonalPlaneIndex := Multiplicative.ofAdd (1 : ZMod 2)
  have hij : (1 : OrthogonalPlaneIndex) ≠ j := by decide
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hp := residualY_isPPerfect M Mc
  have hSY : planeStabilizer T (d.plane 1) ≤ normalizer (residualY M Mc : Set G) :=
    planeStabilizer_normalizes_yplus d T hTM 1 (Or.inl rfl)
  refine ⟨{
    right := centralizingFactor (residualY M Mc) (d.plane 1)
    right_le := le_inf (centralizingFactor_le_left _ _)
      (le_inf ((centralizingFactor_le_left _ _).trans hYM) (centralizingFactor_le _ _))
    right_normal := centralizingFactor_normal (perfect_normalizes_planes d hYM hp 1)
    right_invariant := normalizes_centralizingFactor hSY inf_le_right
    right_perfect := centralizingFactor_isPPerfect _ _
    right_three_part := residual_subgroup_three_part_of_image d
      (centralizingFactor_le_left _ _) h7 h9 (hc.image_card 1)
    left_three_part := residual_subgroup_three_part_of_image d
      (centralizingFactor_le_left _ _) h7 h9 (hc.image_card j)
    generate := residual_plane_generation_of_images d hij.symm h7 h9
      (hc.image_card j) (hc.image_card 1)
    plane := hc.commutator 1 j hij
    plane_self := hc.commutator_self 1 j hij
    other_plane := fun _ => hc.commutator_self j 1 hij.symm
  }, rfl⟩

/-- Construct both residual plane actors in CaseOne from the genuine full
image and the order-nine two-core quotient. The right actor is the literal
two-residual of the centralizer of V₁ in Y. -/
theorem planeActorPair_of_fullAction {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9) :
    ∃ a : PlaneActorPair M (residualY M Mc) (residualY M Mc)
      (planeStabilizer T (d.plane 1)) V (d.plane 1)
      (d.plane (Multiplicative.ofAdd (1 : ZMod 2))),
      a.right = centralizingFactor (residualY M Mc) (d.plane 1) :=
  planeActorPair_of_fullActionCoordinates d T hTM hVM h7 h9
    (residualY_fullActionCoordinateFacts d h7)

end CFSG.Quasithin.Chapter15.Section03.RankTwo
