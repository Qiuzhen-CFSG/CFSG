module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Second.Reapplication

/-!+# Excluding the small branch after a critical shift

The shift supplied by (4.3) gives an actual critical segment through rho.
The binary exclusion in (4.6.11) then supplies the other condition needed
to reapply (4.6.12): its intersection commutator is not contained in Z_alpha.
Indeed, either marking of a single natural quotient of the actual core
contradicts the checked square-map obstruction.

The single-quotient recognition remains an explicit premise here. Its source
proof is owned by the small-intersection branch; this reduction does not
assert that proof or infer non-smallness from escape alone. No containment
of the original orbit span in V_rho is required. Once recognition is proved,
the last theorem discharges the non-smallness premise of SecondStep.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.11), printed p.909, and
the final reapplication paragraph of (4.6.12), printed p.912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- The source single-factor conclusion, with either actual marking, excludes
the small intersection at a selected noncommuting distance-two vertex. The
recognition premise is precisely the output still owed by (4.6.11). -/
theorem shifted_nonSmall_of_singleQuotients (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4)
    (hsmall : ∀ t : CriticalSegment geometry, t.SmallIntersection →
      Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
        Nonempty (SingleQuotient source common Linear.dual))
    (c rho : Vertex R)
    (hc : (cosetGraph R).dist c (alpha R) = 2)
    (hrho : (cosetGraph R).dist (alpha R) rho = 2)
    (hne : ⁅Z R rho, orbitSpan c⁆ ≠ ⊥) :
    ¬ ⁅V R (alpha R) ⊓ Q R rho, V R rho⁆ ≤ Z R (alpha R) := by
  obtain ⟨t, ht⟩ := criticalSegment_through_of_noncommuting source common hb c rho hc hrho hne
  intro hs
  have hts : t.SmallIntersection := by
    simpa only [CriticalSegment.SmallIntersection, ht] using hs
  rcases hsmall t hts with h | h
  · obtain ⟨d⟩ := h
    exact d.natural_impossible radius
  · obtain ⟨d⟩ := h
    exact SingleQuotient.dual_impossible radius d

/-- The preceding source branch suffices to discharge the shifted condition
in the existing second-stage assembly. Its recognition is still explicit. -/
theorem secondStep_of_singleQuotients (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4)
    (hsmall : ∀ t : CriticalSegment geometry, t.SmallIntersection →
      Nonempty (SingleQuotient source common (fun g v => g.val.mulVec v)) ∨
        Nonempty (SingleQuotient source common Linear.dual)) :
    SecondStep source common := by
  apply secondStep_of_shifted_nonSmall source common radius hb
  intro _ s _ _ rho hrho _ hne
  exact shifted_nonSmall_of_singleQuotients source common radius hb hsmall s.middle rho
    ((cosetGraph R).dist_comm.trans s.first_distance)
    ((cosetGraph R).dist_comm.trans hrho.1) hne

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
