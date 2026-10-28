module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Orbit
public import Theory.GroupTheory.PGroup.NormalClosureExtraspecial
public import Theory.ElementaryAbelian.Injective

/-!
# The symplectic critical orbit and its elementary central quotient

The normal closure of the critical plane lies in Q-alpha exactly when the
plane does. The source commutator bound then makes this orbit a group of
nilpotency class at most two. Since the plane is elementary abelian, its
normal closure has elementary abelian central quotient. This gives a binary
module carrier before proving the entire orbit elementary, avoiding a circular
use of elementary-module recognition.

The explicit plane containment is the geometric identity Y = Z-alpha-prime
intersect Q-alpha established during the orbit calculation in MS93 (3.6),
printed p.871. This module proves its group-theoretic consequences.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- The entire orbit is in the two-core exactly when its actual plane is. -/
theorem criticalOrbit_le_Q_iff (hb : s.geometry.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) :
    criticalOrbit R c t ≤ Q R (alpha R) ↔
      criticalPlane R c t ≤ Q R (alpha R) := by
  refine ⟨fun h => (s.criticalPlane_le_orbit hb hc t).trans h,fun h => ?_⟩
  rw [criticalOrbit,Q_alpha R s.two_group s.core_le]
  apply map_mono
  apply normalClosure_le_normal
  intro y hy
  have hh : embedM R y ∈ (pCore 2 M).map (embedM R) := by
    rw [←Q_alpha R s.two_group s.core_le]
    exact h hy
  obtain ⟨x,hx,he⟩ := hh
  exact (embedM_injective R he) ▸ hx

/-- The orbit commutator centralizes the original core before any section
recognition. This is the actual third-commutator bound used on p.871. -/
theorem criticalOrbit_triple_commutator_eq_bot (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    ⁅⁅Q R (alpha R),criticalOrbit R c t⁆,Q R (alpha R)⁆ = ⊥ := by
  apply le_bot_iff.mp
  exact (commutator_mono (s.criticalOrbit_commutator_le hb hc hat hct) le_rfl).trans_eq
    (Z_centralizes_Q R (alpha R) rfl)

/-- Once the critical plane lies in Q-alpha, its orbit has class at most two. -/
theorem criticalOrbitNative_commutator_le_center (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t)
    (hY : criticalPlane R c t ≤ Q R (alpha R)) :
    _root_.commutator (criticalOrbitNative R c t) ≤ center (criticalOrbitNative R c t) := by
  let A := criticalOrbitNative R c t
  have hAQ := (s.criticalOrbit_le_Q_iff hb hc t).mpr hY
  have hAZ : (⁅A,A⁆).map (embedM R) ≤ Z R (alpha R) := by
    rw [map_commutator]
    exact (commutator_mono hAQ le_rfl).trans (s.criticalOrbit_commutator_le hb hc hat hct)
  intro x hx
  apply mem_center_iff.mpr
  intro a
  apply Subtype.ext
  apply embedM_injective R
  change embedM R ((a : M)*(x : M)) = embedM R ((x : M)*(a : M))
  rw [map_mul,map_mul]
  have hxA : (x : M) ∈ ⁅A,A⁆ := by
    rw [←map_subtype_commutator]
    exact mem_map_of_mem A.subtype hx
  have hxZ := hAZ (mem_map_of_mem (embedM R) hxA)
  exact (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q R (alpha R) rfl)) hxZ (embedM R a)
      (hAQ (mem_map_of_mem (embedM R) a.property))

/-- A genuine binary section is available before proving the orbit abelian.
This applies the elementary normal-closure theorem to the actual central quotient. -/
theorem criticalOrbitNative_centerQuotient_elementary (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t)
    (hY : criticalPlane R c t ≤ Q R (alpha R)) :
    IsElementaryAbelian 2 ((criticalOrbitNative R c t) ⧸ center (criticalOrbitNative R c t)) := by
  let := s.criticalPlane_elementary hb hc t
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM R) (embedM_injective R)
    (criticalPlane R c t)
  apply normalClosure_centerQuotient_elementary
  exact Normal.quotient_commutative_iff_commutator_le.mpr
    (s.criticalOrbitNative_commutator_le_center hb hc hat hct hY)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
