module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLargeExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSmallClosure

/-!
# Joining both original cubic plane branches

The actual large-image contradiction transports to every original component
vertex. Hence, at distance four, every critical path has small seed image.
The proved original small-image closure then excludes the whole plane branch
at that distance. The original graph and its cubic covering kernel are retained.
Source: MS93 (5.12), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

/-- The actual large-image contradiction holds at every original component vertex. -/
theorem plane_four_large_impossible_at
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) : False := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hlarge₀ : 4 ≤ (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (act Rg g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have q := p.act g⁻¹
  rw [hbase] at q hlarge₀
  exact plane_four_large_impossible h e hz hk hb u hR q hlarge₀

/-- The original cubic plane cannot have critical distance four; both image
sizes are discharged internally from the original source hypotheses. -/
theorem plane_four_impossible
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom) : False := by
  apply plane_four_uniformly_small_false h e hz hk u hR hb
  intro a z p
  by_contra! hlarge
  exact plane_four_large_impossible_at h e hz hk hb u hR p hlarge

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
