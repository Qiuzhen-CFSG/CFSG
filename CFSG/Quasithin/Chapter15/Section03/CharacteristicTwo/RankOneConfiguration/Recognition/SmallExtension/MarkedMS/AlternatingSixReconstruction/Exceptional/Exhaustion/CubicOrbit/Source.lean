module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Movement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Source

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Recognition.Source

/-!
# Whole-core applications of the cubic critical-plane orbit argument

The checked orbit centralization and three-subgroups calculation reduce the
cubic distance-two branch to the literal plane-intersection bound and an
elementary critical-plane orbit. These explicit premises still require proof
by the alternating-six reconstruction owner. The conclusions below retain
the entire original blockU, its full centralizer and the original C.1.32
rank-two consumer.

The paired exponent-two calculation, actual favorable-pair selection and
exact indices 8, 8 and 4 are proved. The point-core coordinates now establish
full component movement, centrality of the literal fixed kernel and nontrivial
movement of the generating plane. Recognizing the fixed quotient therefore
makes the whole orbit elementary and gives a contradiction. This newer route
requires only recognition; the older conditional interfaces remain available.
Quotient recognition, larger distances and final unconditional reconstruction
remain with the alternating-six reconstruction owner.

Source: MS93 (3.6), pp.870--871; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)

include h e hz hk

open ChapterC in
/-- The two remaining source orbit facts supply every exceptional clause for
the entire intrinsic blockU, including its full centralizer. -/
theorem core_facts_of_distanceTwo_cubic_elementary_orbit
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (hinter : ⁅Q T (alpha T),Z T c ⊓ Q T (alpha T)⁆ ≤ Z T b)
    (hel : IsElementaryAbelian 2 (criticalOrbitNative T c b)) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_elementary_orbit h e hz hk hb hc hab hcb hinter hel)

/-- Apply the orbit calculation to the actual C.1.32 rank-two conclusion.
The literal intersection and elementary-orbit premises remain explicit. -/
theorem rankTwo_of_distanceTwo_cubic_elementary_orbit
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (hinter : ⁅Q T (alpha T),Z T c ⊓ Q T (alpha T)⁆ ≤ Z T b)
    (hel : IsElementaryAbelian 2 (criticalOrbitNative T c b)) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_elementary_orbit h e hz hk hb hc hab hcb hinter hel)

open Natural.Exhaustion.DistanceTwo.Geometry in
/-- Whole-core exhaustion from the actual fixed-quotient recognition.
The paired elementary-commutator premise is now proved internally. The
intersection, recognition and full-movement premises remain with this
reconstruction task; none is asserted to be a finished source theorem. -/
theorem CubicAction.coreExhaustion_of_recognized_paired_orbit
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (hinter : ⁅Q T (alpha T),Z T o.c ⊓ Q T (alpha T)⁆ ≤ Z T o.b)
    (hm : criticalOrbitNative T o.c o.b =
      ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T)
    (hr : o.Recognized) : CoreExhaustion L R := by
  have hp := h.relative_radical.isPGroup
  have hQR := h.relative_radical.twoCore_le
  have hel := CubicAction.paired_commutator_elementary h e hz hk o.distance_two
    o.critical o.adjacent_left o.adjacent_right o.rebased
  have hcent : ⁅⁅pCore 2 M,criticalOrbitNative T o.c o.b⁆,pResidual 2 M⁆ = ⊥ := by
    rw [h.relative_residual]
    exact CubicAction.orbit_commutator_centralizes_component h e hz hk o.distance_two
      o.critical o.adjacent_left o.adjacent_right
  have hfixed := fixedKernel_central_of_full_movement (pResidual 2 M)
    hp hQR o.orbit_le_core hcent hm
  exact CubicAction.coreExhaustion_of_elementary_orbit h e hz hk o.distance_two
    o.critical o.adjacent_left o.adjacent_right hinter
    (o.elementary_of_recognized hp hQR hel hfixed hr)

open ChapterC Natural.Exhaustion.DistanceTwo.Geometry in
/-- Every exceptional clause for the entire original blockU, using the
proved paired exponent calculation and retaining the remaining orbit geometry. -/
theorem core_facts_of_distanceTwo_cubic_recognized_pair
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (hinter : ⁅Q T (alpha T),Z T o.c ⊓ Q T (alpha T)⁆ ≤ Z T o.b)
    (hm : criticalOrbitNative T o.c o.b =
      ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T)
    (hr : o.Recognized) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_recognized_paired_orbit h e hz hk o hinter hm hr)

open Natural.Exhaustion.DistanceTwo.Geometry in
/-- Apply the paired-orbit recognition to the unchanged literal C.1.32
consumer. Final unconditional assembly must discharge its orbit geometry. -/
theorem rankTwo_of_distanceTwo_cubic_recognized_pair
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (hinter : ⁅Q T (alpha T),Z T o.c ⊓ Q T (alpha T)⁆ ≤ Z T o.b)
    (hm : criticalOrbitNative T o.c o.b =
      ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T)
    (hr : o.Recognized) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_recognized_paired_orbit h e hz hk o hinter hm hr)


open Natural.Exhaustion.DistanceTwo.Geometry in
/-- Source selection is now constructed from the original cubic distance-two
hypotheses. The remaining intersection, full movement and recognition facts
refer to this actual selected pair and remain with the reconstruction owner. -/
theorem CubicAction.coreExhaustion_of_selected_orbit_geometry
    (hb : sourceDistance h = 2)
    (hinter : let o := selectedOrbitPair h e hz hk hb
      ⁅Q T (alpha T),Z T o.c ⊓ Q T (alpha T)⁆ ≤ Z T o.b)
    (hm : let o := selectedOrbitPair h e hz hk hb
      criticalOrbitNative T o.c o.b =
        ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T)
    (hr : (selectedOrbitPair h e hz hk hb).Recognized) : CoreExhaustion L R :=
  coreExhaustion_of_recognized_paired_orbit h e hz hk
    (selectedOrbitPair h e hz hk hb) hinter hm hr

open ChapterC Natural.Exhaustion.DistanceTwo.Geometry in
/-- Whole-core consequences on the source-constructed favorable pair.
No existence or paired exponent premise remains. -/
theorem core_facts_of_distanceTwo_cubic_selected_pair
    (hb : sourceDistance h = 2)
    (hinter : let o := CubicAction.selectedOrbitPair h e hz hk hb
      ⁅Q T (alpha T),Z T o.c ⊓ Q T (alpha T)⁆ ≤ Z T o.b)
    (hm : let o := CubicAction.selectedOrbitPair h e hz hk hb
      criticalOrbitNative T o.c o.b =
        ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T)
    (hr : (CubicAction.selectedOrbitPair h e hz hk hb).Recognized) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_selected_orbit_geometry h e hz hk hb hinter hm hr)

open Natural.Exhaustion.DistanceTwo.Geometry in
/-- The original C.1.32 consumer uses the constructed pair and the entire blockU.
Its remaining local geometry is explicit for final source assembly. -/
theorem rankTwo_of_distanceTwo_cubic_selected_pair
    (hb : sourceDistance h = 2)
    (hinter : let o := CubicAction.selectedOrbitPair h e hz hk hb
      ⁅Q T (alpha T),Z T o.c ⊓ Q T (alpha T)⁆ ≤ Z T o.b)
    (hm : let o := CubicAction.selectedOrbitPair h e hz hk hb
      criticalOrbitNative T o.c o.b =
        ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T)
    (hr : (CubicAction.selectedOrbitPair h e hz hk hb).Recognized) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_selected_orbit_geometry h e hz hk hb hinter hm hr)


open Natural.Exhaustion.DistanceTwo.Geometry in
/-- The remaining source geometry on pairs with the now-proved exact indices.
Final unconditional reconstruction must prove this local assertion; it contains
neither whole-core exhaustion nor a block conclusion. -/
def CubicAction.BoundedOrbitGeometry : Prop :=
  ∀ o : BeforePlane.PreliminaryPair T (sourceGeometry h), o.b = beta T →
    (Q T (alpha T)).relIndex o.opposite = 8 →
    (Q T o.c).relIndex (criticalOrbit T o.c o.b) = 8 →
    (commutatorPreimage (criticalOrbit T o.c o.b) o.opposite (Z T (alpha T))).relIndex
      (criticalOrbit T o.c o.b) = 4 →
    (⁅Q T (alpha T),Z T o.c ⊓ Q T (alpha T)⁆ ≤ Z T o.b) ∧
    (criticalOrbitNative T o.c o.b =
      ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T) ∧ o.Recognized

/-- The exact orbit indices are supplied internally to their remaining
geometric consumer, which then exhausts the literal entire original core. -/
theorem CubicAction.coreExhaustion_of_bounded_orbit_geometry
    (hb : sourceDistance h = 2) (hgeometry : BoundedOrbitGeometry h) : CoreExhaustion L R := by
  let o := selectedOrbitPair h e hz hk hb
  obtain ⟨h8,h8',h4⟩ := selectedOrbitPair_indices h e hz hk hb
  obtain ⟨hi,hm,hr⟩ := hgeometry o (selectedOrbitPair_base h e hz hk hb) h8 h8' h4
  exact coreExhaustion_of_recognized_paired_orbit h e hz hk o hi hm hr

open ChapterC in
/-- Whole-core application of the exact favorable-pair orbit bound. The
remaining bounded geometry is owned by this reconstruction task. -/
theorem core_facts_of_distanceTwo_cubic_bounded_geometry
    (hb : sourceDistance h = 2) (hgeometry : CubicAction.BoundedOrbitGeometry h) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_bounded_orbit_geometry h e hz hk hb hgeometry)

/-- Apply the exact orbit bounds to the original C.1.32 conclusion, retaining
its whole-core clauses and the explicit unproved local geometric premise. -/
theorem rankTwo_of_distanceTwo_cubic_bounded_geometry
    (hb : sourceDistance h = 2) (hgeometry : CubicAction.BoundedOrbitGeometry h) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_bounded_orbit_geometry h e hz hk hb hgeometry)

open ChapterC Natural.Exhaustion.DistanceTwo.Geometry in
/-- All whole-core clauses follow from recognition of the source-selected
orbit quotient. Plane movement and fixed-kernel centrality are now proved;
this owner still discharges recognition before unconditional assembly. -/
theorem core_facts_of_distanceTwo_cubic_selected_recognition
    (hb : sourceDistance h = 2)
    (hr : (CubicAction.selectedOrbitPair h e hz hk hb).Recognized) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_selected_recognition h e hz hk hb hr)

open Natural.Exhaustion.DistanceTwo.Geometry in
/-- The reduced orbit-recognition obligation feeds the unchanged C.1.32
consumer with its literal entire core and both block alternatives. -/
theorem rankTwo_of_distanceTwo_cubic_selected_recognition
    (hb : sourceDistance h = 2)
    (hr : (CubicAction.selectedOrbitPair h e hz hk hb).Recognized) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_selected_recognition h e hz hk hb hr)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
