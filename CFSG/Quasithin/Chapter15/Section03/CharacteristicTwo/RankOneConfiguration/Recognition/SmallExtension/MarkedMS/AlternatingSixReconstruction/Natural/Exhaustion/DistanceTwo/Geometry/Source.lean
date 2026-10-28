module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Core
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Selection

/-!
# Conditional assembly of paired critical orbits with their central attachment

The local source identities select favorable genuine orbits. The paired
estimate then supplies their full edge image and plane movement. Normal
closure, the two-group supplement argument and three-subgroups produce full
component movement, the central fixed kernel and a nonfixed plane seed.
These give every field of the literal PairedOrbit, on the replacement carrier.

Both source-calculation inputs remain obligations for the original marked
pair. This module proves their assembly, not their unconditional existence.
The last theorem applies the resulting orbit to the explicit recognition
input and obtains the actual distance-two exhaustion conclusion.
Source: MS93 (3.3), (3.6), printed pp.866--871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geo : Geometry R)

/-- Source local movement excludes a fixed generating plane in the genuine
non-Frattini branch. -/
theorem plane_not_fixed (hl : LocalCalculations R geo) (hb : geo.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel (pResidual 2 M) R c b := by
  apply plane_not_fixed_of_movement
  intro hm
  have hh := map_mono (f := embedM R) hm
  rw [map_commutator,←Ltilde_alpha] at hh
  change ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ ≤ _ at hh
  rw [hl.commutator_core c b hc hab hcb] at hh
  have hZ : Z R (alpha R) ≤ X R (alpha R) :=
    geo.omega_bound (alpha R) rfl (by change 0 < geo.b R; omega)
  exact hlarge (((hh.trans (map_comap_le _ _)).trans hZ).trans le_sup_right)

/-- Construct all orbit fields from local identities and the paired
calculation, preserving the chosen opposite subgroup and literal kernels. -/
def pairedOrbit (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hgen : pResidual 2 M ⊔ R = ⊤) (hl : LocalCalculations R geo)
    (hb : geo.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    (o : OrderedOrbit geo) (he : PairEstimates R o.c o.b o.opposite) :
    PairedOrbit (pResidual 2 M) R geo := by
  have hA := hl.orbit_core o.c o.b o.critical o.adjacent_left o.adjacent_right
  have hm := full_movement_of_plane geo (pResidual 2 M) hp hgen hb
    o.critical o.adjacent_left o.adjacent_right hA he.moved_plane
  have hn := plane_not_fixed geo hl hb hlarge o.critical o.adjacent_left o.adjacent_right
  exact {
    c := o.c, b := o.b, opposite := o.opposite
    distance_two := hb, critical := o.critical
    adjacent_left := o.adjacent_left, adjacent_right := o.adjacent_right
    orbit_le_core := hA
    layer_le := layer_le_orbit geo hb o.critical o.adjacent_left o.adjacent_right
    full_movement := hm
    commutator_le_layer := orbit_commutator_le_layer geo hp hQR hb
      o.critical o.adjacent_left o.adjacent_right
    opposite_le := o.opposite_le
    opposite_normalized := o.opposite_normalized
    commutator_elementary := he.elementary_commutator
    opposite_commutator := o.opposite_commutator
    opposite_movement := o.opposite_movement
    strict_index := o.strict_index, ordered_index := o.ordered_index
    full_image := he.full_image
    fixed_central := fixedKernel_central_of_full_movement (pResidual 2 M) hp hQR hA
      (hl.commutator_central o.c o.b o.critical o.adjacent_left o.adjacent_right) hm
    plane_not_fixed := hn
    movement := plane_movement_of_full_image geo (pResidual 2 M) hb
      o.critical o.adjacent_left o.adjacent_right he.full_image hn }

/-- Final assembly within this task: both independent source calculations
must be discharged before this becomes the requested geometry input. -/
theorem orbitGeometry_of_calculations {κ : GroupClass.{u}}
    (hl : LocalCalculationInput κ) (he : PairEstimateInput κ) : OrbitGeometryInput κ := by
  intro G _ _ L R h e hz hn d hc hb hlarge
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  have hgen := replacement_residual_sup_radical h d
  have hlocal := hl G L R h e hz hn d hc hb hlarge
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d) hp hQR hlocal hb
  have hestimate := he G L R h e hz hn d hc hb hlarge hlocal o.c o.b o.opposite
    o.critical o.adjacent_left o.adjacent_right o.rebased o.strict_index o.ordered_index
  exact ⟨pairedOrbit (replacementGeometry h d) hp hQR hgen hlocal hb hlarge o hestimate⟩

/-- The two remaining source inputs suffice on the original marked pair;
no natural-subgroup or full point-image premise is added. -/
theorem orbitGeometry_of_structure {κ : GroupClass.{u}}
    (hs : LocalStructureInput κ) (he : PairEstimateInput κ) : OrbitGeometryInput κ :=
  orbitGeometry_of_calculations (localCalculationInput_of_structure hs) he

/-- The actual recognition consumer rules out the unresolved branch for
the same replacement, without asserting that recognition is already proved. -/
theorem false_of_calculations_and_recognition {κ : GroupClass.{u}}
    (hl : LocalCalculationInput κ) (he : PairEstimateInput κ) (hr : OrbitRecognitionInput κ)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hc : CentralLayer d) (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical)) : False := by
  obtain ⟨o⟩ := orbitGeometry_of_calculations hl he G L R h e hz hn d hc hb hlarge
  exact o.false_of_recognized (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d) (hr G L R h e hz hn d hc hb hlarge o)

/-- Concrete exhaustion consumer, including the independent Frattini branch. -/
theorem exhaustion_of_calculations_and_recognition {κ : GroupClass.{u}}
    (hl : LocalCalculationInput κ) (he : PairEstimateInput κ) (hr : OrbitRecognitionInput κ)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hc : CentralLayer d) (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R := by
  by_cases hf : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical)
  · exact exhaustion_of_frattini h d hc hf
  · exact (false_of_calculations_and_recognition hl he hr h e hz hn d hc hb hf).elim

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
