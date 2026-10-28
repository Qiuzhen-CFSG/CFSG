module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongWitness
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongTerminal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneExclusion

/-!
# Excluding the original cubic plane at every distance

Above distance four the selected original paths supply an interior-generating
radius of index four, contradicting its conjugate-kernel control. Parity and
the distance-two exclusion then reduce the remaining plane to the completed
distance-four contradiction. The original cubic quotient E/Q is retained.
Source: MS93 (5.11)--(5.12), printed pp.923--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

/-- The actual original plane has no critical distance above four. -/
theorem plane_distance_le_four (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) :
    sourceDistance h ≤ 4 := by
  by_contra! hb
  obtain ⟨a,z,p,hgen,hfour⟩ :=
    plane_long_exists_generated_radius_four h e hz hk hb u hR
  exact plane_long_generated_radius_ne_four h e hz hk hb u hR p hgen hfour

/-- The literal plane image of the original cubic radical is impossible. -/
theorem plane_image_impossible (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) : False := by
  have hle := plane_distance_le_four h e hz hk u hR
  have hgt := distance_gt_two h e hz hk
  have he := sourceDistance_even h
  rw [Nat.even_iff] at he
  have hb : sourceDistance h = 4 := by omega
  exact plane_four_impossible h e hz hk hb u hR

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
