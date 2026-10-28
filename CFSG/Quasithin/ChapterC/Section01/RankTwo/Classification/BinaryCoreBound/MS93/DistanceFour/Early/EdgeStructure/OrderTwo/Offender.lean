module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer
public import Theory.Frattini.PGroup

/-!
# The actual quotient offender in the order-two exclusion

The critical endpoint supplies an elementary actor inside the first edge
kernel, outside the initial kernel, with trivial intrinsic Frattini subgroup.
A commutator bound on V_alpha intersect Q_c bounds the fixed-subgroup index
on the actual quotient V_alpha/Z_alpha, with the actor retained inside the
local stabilizer. Finally, any offender contradicts V_alpha' <= D_alpha:
the initial offender implication places V_alpha' in U_alpha, whose
intersection with the component centralizer is trivial, while the escape
theorem makes V_alpha nonabelian.

These are conditional steps in MS93 (1993), (4.6.5), p.903. They do not
construct the remaining offender index estimate or the derived fixedness
deduced there from (2.3).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common

/-- The source critical endpoint is an actual eligible actor, including its
intrinsic Frattini containment. The index inequality remains to be proved. -/
theorem critical_actor (a a' : Vertex R) (ha : color R a = false)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ∃ b, Adjacent R a b ∧ Z R a' ≤ Q R b ∧ ¬ Z R a' ≤ Q R a ∧
      (frattini (Z R a')).map (Z R a').subtype ≤ Q R a := by
  have ha' := critical_endpoint_color R a ha _ hcrit
  have hpos : 0 < geometry.b R := lt_trans (by decide) common.large_distance
  obtain ⟨b, hab, _, _, hAb⟩ := critical_first_neighbor R geometry a ha
    (by rw [geometry.distance_constant a ha]; exact hpos) hcrit
  refine ⟨b, hab, hAb, (common.critical_reverse a ha a' ha' hcrit).2, ?_⟩
  let : Finite (stabilizer R a') := finite_stabilizer R a'
  let : Finite (Z R a') := Finite.of_injective (inclusion (Z_le_stabilizer R a'))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z R a') := geometry.Z_elementary hpos a' ha'
  have hZQ : Z R a' ≤ Q R a' := by
    rw [← common.X_eq_Z a' ha']
    exact omegaCenter_le _
  let : Fact (IsPGroup 2 (Z R a')) := ⟨(Q_isPGroup R source.two_group
    source.core_le a' ha').of_injective (inclusion hZQ) (inclusion_injective hZQ)⟩
  rw [frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
  exact bot_le

/-- A subgroup centralizing the actor modulo Z bounds the actual quotient
fixed index; the right side is [V_alpha : V_alpha intersect Q_c]. -/
theorem fixed_index_le_of_commutator (a c : Vertex R) (ha : color R a = false)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a)
    (hcomm : ⁅V R a ⊓ Q R c, A⁆ ≤ Z R a) :
    (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R c).relIndex (V R a) := by
  let : Finite (V R a) := finite_radius common a ha
  have hle : V R a ⊓ Q R c ≤ radiusFixed geometry a A := by
    intro x hx
    apply (mem_radiusFixed_iff common a ha A hA x).mpr
    refine ⟨hx.1, fun g hg => ?_⟩
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator hg hx)
  have hi := relIndex_le_of_le_left hle
    (show ((V R a ⊓ Q R c).subgroupOf (V R a)).index ≠ 0 from index_ne_zero_of_finite)
  simpa only [inf_relIndex_left] using hi

/-- Source (4.6.2) and the nonabelian radius group exclude a genuine offender
once the derived subgroup has been proved component-fixed. -/
theorem not_offender_of_derived_fixed (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry) (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R b) (hnot : ¬ A ≤ Q R a)
    (hPhi : (frattini A).map A.subtype ≤ Q R a) :
    ¬ (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A := by
  intro hi
  have hU := initial.offender_derived_le a b ha hab A hA hnot hPhi hi
  apply radius_derived_ne_bot common hb a ha
  exact le_bot_iff.mp ((le_inf hU (hfixed.trans inf_le_right)).trans
    (Flags.U_fixed_eq_bot common a ha).le)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo
