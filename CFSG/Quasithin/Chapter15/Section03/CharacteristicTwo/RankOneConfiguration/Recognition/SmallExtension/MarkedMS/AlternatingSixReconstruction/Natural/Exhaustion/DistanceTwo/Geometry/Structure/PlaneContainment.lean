module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Preparation

/-!
# The maximal critical plane is inside the kernel

In the non-Frattini branch the normal orbit of the maximal plane cannot
escape the two-core: normal generation would put the residual in that orbit,
and the edge commutator bound would put the entire graph core in its central
omega layer. Pulling this conclusion through the actual amalgam embedding
gives one inclusion in the source's maximal-plane identity.

Source: MS93 (3.6), printed pp.870--871. This direction uses neither
the full point-core image nor a splitting of the natural central cover.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (d : Replacement L R)
  (hb : replacementDistance h d = 2)
  (hlarge : ¬ core d.radical (alpha d.radical) ≤
    (frattini (Q d.radical (alpha d.radical))).map
      (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
  {c b : Vertex d.radical}
  (hc : CriticalPair d.radical (alpha d.radical) c
    ((replacementGeometry h d).exists_critical _ rfl))
  (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b)

include h e hz hb hlarge hc hab hcb in
/-- Normal generation and the edge bound alone put the entire plane orbit
in the actual replacement two-core. -/
theorem replacement_orbit_le_core :
    criticalOrbitNative d.radical c b ≤ pCore 2 d.overgroup := by
  by_contra hn
  have hK := replacement_normal_generation h e hz d
    (criticalOrbitNative d.radical c b) hn
  have hKg : Ltilde d.radical (alpha d.radical) ≤ criticalOrbit d.radical c b := by
    rw [Ltilde_alpha]
    exact map_mono hK
  have hcore : core d.radical (alpha d.radical) ≤ Z d.radical (alpha d.radical) :=
    (commutator_mono le_rfl hKg).trans
      (criticalOrbit_commutator_le (replacementGeometry h d)
        (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hb hc hab hcb)
  have hZ := (replacementGeometry h d).omega_bound (alpha d.radical) rfl
    (by change 0 < replacementDistance h d; omega)
  exact hlarge (hcore.trans (hZ.trans le_sup_right))

include h e hz hb hlarge hc hab hcb in
/-- The upper inclusion in the literal maximal-plane identity. -/
theorem replacement_plane_le_intersection :
    criticalPlane d.radical c b ≤ Z d.radical c ⊓ Q d.radical (alpha d.radical) := by
  apply le_inf (criticalPlane_le_opposite c b)
  apply (criticalPlane_le_orbit (replacementGeometry h d) hb hc b).trans
  rw [criticalOrbit, Q_alpha d.radical
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
  exact map_mono (replacement_orbit_le_core h e hz d hb hlarge hc hab hcb)

include h e hz hb hlarge hc hab hcb in
/-- The only remaining inclusion is exactly the source intersection's
edge commutator bound; no equality of abstract model tags is used. -/
theorem replacement_plane_eq_of_intersection_bound
    (hcomm : ⁅Q d.radical (alpha d.radical),
        Z d.radical c ⊓ Q d.radical (alpha d.radical)⁆ ≤ Z d.radical b) :
    criticalPlane d.radical c b = Z d.radical c ⊓ Q d.radical (alpha d.radical) := by
  apply le_antisymm (replacement_plane_le_intersection h e hz d hb hlarge hc hab hcb)
  exact le_criticalPlane_of_commutator_le _ inf_le_left hcomm

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
