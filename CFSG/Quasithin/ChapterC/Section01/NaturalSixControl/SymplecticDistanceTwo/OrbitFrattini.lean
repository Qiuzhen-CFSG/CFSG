module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitKernel
public import Theory.Frattini.NormalClosureElementary
public import Theory.Frattini.FiniteIntersection

/-!
# Frattini bounds and elementary intersections of the critical orbits

The elementary critical plane normally generates A, so A/[Qalpha,A] is
elementary and Phi(A) lies in [Qalpha,A]. The latter centralizes Lalpha.
For the opposite orbit, its Frattini subgroup lies in Ualpha, which has no
component-fixed vectors. The two Frattini bounds are disjoint, so their
common subgroup is elementary even inside the infinite free amalgam.
Source: MS93 (3.6), the Frattini calculation on printed p.871.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem criticalOrbitNative_frattini_le_commutator
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    (frattini (criticalOrbitNative R c b)).map (criticalOrbitNative R c b).subtype ≤
      ⁅pCore 2 M,criticalOrbitNative R c b⁆ := by
  let := s.criticalPlane_elementary hb hc b
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM R) (embedM_injective R)
    (criticalPlane R c b)
  exact normalClosure_frattini_image_le_commutator
    ((criticalPlane R c b).comap (embedM R)) (pCore 2 M) pCore_isPGroup
    (s.criticalOrbitNative_le_core_of_core_ne hb hc hab hcb hne)

theorem criticalOrbit_frattini_le_commutator
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    (frattini (criticalOrbit R c b)).map (criticalOrbit R c b).subtype ≤
      ⁅Q R (alpha R),criticalOrbit R c b⁆ := by
  change (frattini ((criticalOrbitNative R c b).map (embedM R))).map
    ((criticalOrbitNative R c b).map (embedM R)).subtype ≤
      ⁅Q R (alpha R),(criticalOrbitNative R c b).map (embedM R)⁆
  rw [frattini_image_map _ _ (embedM_injective R),Q_alpha R s.two_group s.core_le,
    ←map_commutator]
  exact map_mono (s.criticalOrbitNative_frattini_le_commutator hb hc hab hcb hne)

theorem paired_orbit_frattini_disjoint (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R))
    (B : Subgroup (FreeAmalgam R))
    (hB : (frattini B).map B.subtype ≤ U R (alpha R)) :
    Disjoint ((frattini (criticalOrbit R c b)).map (criticalOrbit R c b).subtype)
      ((frattini B).map B.subtype) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  have hcA : (frattini (criticalOrbit R c b)).map (criticalOrbit R c b).subtype ≤
      centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) :=
    (s.criticalOrbit_frattini_le_commutator hb hc hab hcb hne).trans
      (commutator_eq_bot_iff_le_centralizer.mp
        (s.criticalOrbit_commutator_centralizes_residual t hfull hb hc hab hcb hne))
  exact (le_inf (inf_le_right.trans hB) (inf_le_left.trans hcA)).trans_eq
    (s.movingLayer_inf_component_centralizer_eq_bot h)

theorem paired_orbit_intersection_elementary (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R))
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hB : (frattini B).map B.subtype ≤ U R (alpha R)) :
    IsElementaryAbelian 2 (criticalOrbit R c b ⊓ B : Subgroup (FreeAmalgam R)) := by
  let A := criticalOrbit R c b
  have hAQ : A ≤ Q R (alpha R) := (s.criticalOrbit_le_Q_iff hb hc b).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (stabilizer R c) := finite_stabilizer R c
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  let : Finite B := Finite.of_injective
    (inclusion (hBQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hAp : IsPGroup 2 A :=
    (Q_isPGroup R s.two_group s.core_le (alpha R) rfl).of_injective
      (inclusion hAQ) (inclusion_injective _)
  have hBp : IsPGroup 2 B :=
    (Q_isPGroup R s.two_group s.core_le c (critical_endpoint_color R (alpha R) rfl _ hc)).of_injective
      (inclusion hBQ) (inclusion_injective _)
  exact finite_common_subgroup_elementary_of_disjoint_frattini hAp hBp inf_le_left inf_le_right
    (s.paired_orbit_frattini_disjoint h t hfull hb hc hab hcb hne B hB)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
