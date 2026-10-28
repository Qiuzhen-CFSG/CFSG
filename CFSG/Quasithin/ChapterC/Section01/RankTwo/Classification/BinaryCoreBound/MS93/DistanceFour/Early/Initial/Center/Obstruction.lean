module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Pairing
public import Theory.Representation.PSL3Two.ResidualFFForms

/-!
# The binary obstruction after the radius-derived group is fixed

If the local residual fixes V', scalar forms of the commutator pairing on
P/Z(P), for P = [V,Ltilde], are residual-invariant and have zero common
radical. A projected binary SL3 offender forces all these forms to vanish
by the simple-constituent cost bounds, including nonsplit modules with
nontrivial two-core action. Thus P is abelian. Residual commutator generation
makes it central in V, and the abelian edge-radius supplement makes V
abelian, contradicting the distance-four escape theorem.

The displacement comparison transfers any offender on the actual V/Z(V)
to P/Z(P). This gives the final binary contradiction in (4.6.1), conditional
on its two geometric inputs: residual fixation of V' and the source
central-quotient offender. Neither input is asserted here under failure
of the center containment. No self-duality or elementary lift is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.4), (3.8)--(3.9), and (4.6.1), pp.842, 878--879, 900--901.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
open NaturalStructure.Exclusion

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual moving central quotient cannot have a projected offender when
the radius-derived subgroup is fixed by the local residual. The actor itself
need not be elementary abelian; only its specified quotient image does. -/
theorem false_of_moving_offender_of_derived_fixed (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a)
    (π : stabilizer R a →* SL) (hπ : Function.Surjective π)
    (hker : π.ker = (Q R a).subgroupOf (stabilizer R a))
    (A : Subgroup (stabilizer R a)) (hA : IsElementaryAbelian 2 (A.map π))
    (hmap : A.map π ≠ ⊥)
    (hcost : letI := moving_central_quotient_elementary geometry (by omega) a ha hfixed
      fixedCodim (Offenders.linearize (movingQuotientAction a)) A ≤ rank (A.map π)) : False := by
  let := moving_central_quotient_elementary geometry (by omega) a ha hfixed
  let := finite_stabilizer R a
  let := finite_moving geometry common.large_distance a ha
  let ρ := Offenders.linearize (movingQuotientAction a)
  have hp : IsPGroup 2 π.ker := by
    rw [hker]
    exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
  obtain ⟨forms, _, hsep, hinv⟩ :=
    movingQuotient_separating_forms geometry (by omega) a ha hfixed
  have hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
    apply top_unique
    calc
      (⊤ : Submodule (ZMod 2) (Additive ((Vcirc R a) ⧸ center (Vcirc R a)))) =
          subspaceCommutator ρ ⊤ (pResidual 2 (stabilizer R a)) :=
        (movingQuotientAction_full source geometry common.large_distance a ha hfixed).symm
      _ ≤ subspaceCommutator ρ ⊤ ⊤ := by
        apply Submodule.span_mono
        rintro _ ⟨g, _, v, hv, rfl⟩
        exact ⟨g, Subgroup.mem_top _, v, hv, rfl⟩
  have hzero (B) (hB : B ∈ forms) : B = 0 := by
    apply BinaryLinearThree.ResidualFFForms.form_zero_of_residual_invariance ρ ?_ B
      (hinv · · B hB)
    intro C hC
    exact BinaryLinearThree.ResidualFFForms.form_zero_of_simpleBudget ρ A (rank (A.map π))
      (BinaryLinearThree.ResidualFFForms.simpleBudget_of_surjective π hπ hp A _
        (BinaryLinearThree.ResidualFFForms.simpleBudget _ hmap hA)) hcost hfull C hC
  have hvzero (v : Additive ((Vcirc R a) ⧸ center (Vcirc R a))) : v = 0 := by
    apply hsep v
    intro B hB w
    rw [hzero B hB]
    rfl
  have hc : IsMulCommutative (Vcirc R a) := by
    apply le_centralizer_iff_isMulCommutative.mp
    intro x hx y hy
    have hq := hvzero (Additive.ofMul
      (QuotientGroup.mk' (center (Vcirc R a)) ⟨x,hx⟩))
    have hxc : (⟨x,hx⟩ : Vcirc R a) ∈ center (Vcirc R a) :=
      (QuotientGroup.eq_one_iff _).mp hq
    exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨y,hy⟩)
  have hcentral := moving_central_of_commutative source geometry common.large_distance
    a ha hfixed hc
  obtain ⟨a', hcrit⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  obtain ⟨t, hat, _⟩ := exists_adjacent_dist_sub_one R a a' (by
    rw [hcrit.1, geometry.distance_constant a ha]
    exact lt_trans (by decide : 0 < 2) common.large_distance)
  exact radius_not_commutative common hb a ha
    (radius_commutative_of_moving_central source geometry common.large_distance a t ha hat hcentral)

/-- The final binary obstruction for the source quotient V/Z(V).
The two geometric premises in (4.6.1) must be constructed separately. -/
theorem not_radiusCenterOffender_of_derived_fixed
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a) :
    ¬ HasRadiusCenterOffender common hb a ha := by
  let := radiusCenterQuotient_elementary common hb a ha
  let := moving_central_quotient_elementary geometry (by omega) a ha hfixed
  rintro ⟨π, A, hπ, hker, hA, hmap, hcost⟩
  exact false_of_moving_offender_of_derived_fixed common hb a ha hfixed π hπ hker A hA hmap
    ((moving_fixedCodim_le_radiusCenter common hb a ha hfixed A).trans hcost)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
