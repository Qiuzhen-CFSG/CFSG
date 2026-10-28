module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.PlaneContainment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Noncontainment

/-!
# Assembly of the original distance-two local structure

The proved simple-component argument supplies edge centralizers and normal
generation. The maximal-plane upper inclusion is also unconditional in the
original non-Frattini branch. The remaining two finite-action source inputs
supply its lower inclusion, the abelian edge quotient and critical index.
Their assembly discharges every field of the literal local-calculation
consumer. The inputs themselves remain source obligations.

Source: MS93 (3.3), (3.6), printed pp.866--871.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {κ : GroupClass.{u}}

/-- Both independent finite-action source branches suffice for the requested
local structure, with every original hypothesis retained. -/
theorem localStructure_of_source_inputs
    (hi : LocalImageInput κ) (hp : PlaneIntersectionInput κ) : LocalStructureInput κ := by
  intro G _ _ L R h e hz hn d hl hb hlarge
  have him := hi G L R h e hz hn d hl hb hlarge
  exact {
    edge_centralizer := replacement_edge_centralizer h e hz d
    normal_generation := replacement_normal_generation h e hz d
    radical_derived := him.radical_derived
    plane_eq := fun c b hc hab hcb =>
      replacement_plane_eq_of_intersection_bound h e hz d hb hlarge hc hab hcb
        (hp G L R h e hz hn d hl hb hlarge him c b hc hab hcb)
    image_two := him.image_two }

/-- Literal replacement consumer: all six orbit-calculation fields follow
once the two specified source calculations have been proved. -/
theorem localCalculationInput_of_source_inputs
    (hi : LocalImageInput κ) (hp : PlaneIntersectionInput κ) : LocalCalculationInput κ :=
  localCalculationInput_of_structure (localStructure_of_source_inputs hi hp)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
