module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases

/-!
# Coordinates and definite planes on the original source action

The non-S₃ classification intersection supplies both the Thompson residual
identity and the four surviving full quotients. Adding that proved residual
to the original source record preserves its literal offender representation.
The action recognizer therefore consumes the same corrected B.5 witness and
constructs the full hexacode coordinates. The marked-plane theorem applies
to those coordinates on the actual ambient definite planes restricted to G₀.

The earlier local configuration and the genuine classifier witnesses remain
inputs. No residual identity, surviving quotient, representation equivalence,
scalar-plane assertion or plane orbit is an additional hypothesis of the
non-S₃ implication below. The S₃ contradiction and the discharge of the
earlier source inputs belong to the assembly of Theorem 15.3.1.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.1155 (PDF p.1172), using B.5.1/B.5.6 and the conventions of A.3.5/K.1.3.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition

open ExceptionalAction
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

universe u

namespace Intersection.SourceInput

variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The corrected classifiers on the actual source actors construct coordinates
in the non-S₃ branch, discharging the residual and four-way quotient premises. -/
theorem nonempty_coordinates_of_source_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : Intersection.SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Nonempty (HexacodeCoordinates V d.centralizer_isTwoGroup d.core_centralizes) := by
  have h := d.source_nonS3_cases_of_classifications hF hB hnot
  exact (d.toActionInput h.residual).nonempty_coordinates_of_surviving_source h.quotient hB

/-- Specialization of the full adequate F.6.18 and B.5 classification inputs.
The B.5 witness is applied to the literal offender action, not the full quotient. -/
theorem nonempty_coordinates_of_full_source_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Nonempty (HexacodeCoordinates V d.centralizer_isTwoGroup d.core_centralizes) :=
  d.nonempty_coordinates_of_source_classifications
    (d.full_goldschmidt_alternative hH classificationF)
    (d.full_sourceFF_alternative hH classificationB) hnot

end Intersection.SourceInput

namespace ExceptionalAction

variable {G : Type u} [Group G] [Finite G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]

/-- Conditional recognition from the genuine surviving quotient and FF inputs.
Both definite planes are recognized in the same constructed coordinates. -/
theorem exists_coordinates_and_planes_of_surviving_source
    (a : ActionRecognition.SourceInput (V.subgroupOf G₀))
    (cfg : MarkedPlane.SourceConfiguration G₀ M V d)
    (quotient : Cases.SurvivingQuotientAlternative (coreQuotient G₀))
    (classification : Intersection.SourceFFAlternative a.offenderAction) :
    ∃ c : HexacodeCoordinates (V.subgroupOf G₀)
        a.centralizer_isTwoGroup a.core_centralizes,
      ∀ i : OrthogonalPlaneIndex, Representation.Hexacode.IsFullWeightScalarPlane
        ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
          c.vectors.toLinearMap) := by
  obtain ⟨c⟩ := a.nonempty_coordinates_of_surviving_source quotient classification
  exact ⟨c, MarkedPlane.localPlane_isFullWeightScalarPlane c cfg⟩

/-- Full conditional non-S₃ recognition on the original intrinsic source input.
The coordinate producer discharges the representation, cover-comparison,
Thompson-image and surviving-quotient obligations before recognizing the planes. -/
theorem exists_coordinates_and_planes_of_full_source_classifications
    (a : Intersection.SourceInput (V.subgroupOf G₀))
    (cfg : MarkedPlane.SourceConfiguration G₀ M V d)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup G₀).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    ∃ c : HexacodeCoordinates (V.subgroupOf G₀)
        a.centralizer_isTwoGroup a.core_centralizes,
      ∀ i : OrthogonalPlaneIndex, Representation.Hexacode.IsFullWeightScalarPlane
        ((planeSubspace (V.subgroupOf G₀) (localPlane G₀ M V d i)).map
          c.vectors.toLinearMap) := by
  obtain ⟨c⟩ := a.nonempty_coordinates_of_full_source_classifications
    hG₀ classificationF classificationB hnot
  exact ⟨c, MarkedPlane.localPlane_isFullWeightScalarPlane c cfg⟩

end ExceptionalAction
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
