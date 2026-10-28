module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.CentralOrbit
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
/-!
# Full-orbit odd linear-three exclusion without a fixed-space restriction

The actual component image in Aut_LT(<Vᵀ>) is quasisimple and is its
generalized Fitting subgroup. The original chosen Irr⁺ subspace remains
Irr⁺ on that orbit. Its irreducible central image has degree greater than
eighteen, while cubic ratio at most two forces the component-fixed
codimension to be at most eighteen. This excludes both zero and nonzero
fixed-space cases, without requiring the whole orbit to be irreducible.

Only the original Hypothesis 12.2.1 and the literal linear-three quotient
are used. The independent earlier 3.1.8 bound on this same whole-orbit
action is retained in the elimination consumer; no seven-model list or
module-normalization conclusion is assumed.
Source: Aschbacher--Smith, 13.1.4, p.867, and 3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {T : Sylow 2 G} {L V : Subgroup G}
private theorem linearThree_central_quotient {Q : Type u} [Group Q]
    [IsQuasisimple Q] {p : ℕ} (hm : LinearThreeModel p Q) :
    ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p := by
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  rcases hm with ⟨F, hF, hfin, hc, ⟨e⟩⟩ | ⟨F, hF, hfin, hc, ⟨e⟩⟩
  · let : Nontrivial (Matrix.SpecialLinearGroup (Fin 3) F) := e.injective.nontrivial
    exact ⟨F, hF, hfin, hc,
      ⟨IsQuasisimple.centralQuotientEquiv e.toMonoidHom e.surjective⟩⟩
  · let S := Matrix.SpecialLinearGroup (Fin 3) F
    let P := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F
    let : Group.IsPerfect S := Atlas.sl_perfect 3 (by decide)
    have hz : center P = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot S
    exact ⟨F, hF, hfin, hc, ⟨(IsQuasisimple.centralQuotientEquiv e.toMonoidHom
      e.surjective).trans ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot)⟩⟩

/-- The actual full-orbit obstruction, including seeds with nonzero fixed space. -/
theorem linear_three_whole_orbit_cubicRatio_gt_two (D : ChosenModule T L V)
    (h : Hypothesis1221 κ T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hm : LinearThreeModel p (XiQuotient L)) :
    2 < cubicRatio D.orbitRepresentation := by
  let := h.quasisimple
  let := D.orbitComponent_quasisimple h
  have hmO := (linearThree_central_quotient hm).of_mulEquiv
    (D.orbitCentralQuotientEquiv h).symm
  have hmF : ClassicalGroup.IsPSL
      ((generalizedFitting D.orbitActor) ⧸ center (generalizedFitting D.orbitActor)) 3 p :=
    (congrArg (fun X : Subgroup D.orbitActor => ClassicalGroup.IsPSL
      (X ⧸ center X) 3 p) (D.orbit_fitting h)).mpr hmO
  have hqF : IsQuasisimple (generalizedFitting D.orbitActor) :=
    (congrArg (fun X : Subgroup D.orbitActor => IsQuasisimple X)
      (D.orbit_fitting h)).mpr (D.orbitComponent_quasisimple h)
  have hI : IsIrrPlus D.orbitRepresentation D.orbitComponent
      (D.space.comap D.orbitSpace.subtype) :=
    D.irrPlus.isIrrPlus.restricted _ D.orbitSpace_component_invariant D.seed_le_orbitSpace
  have hp5 : 5 ≤ p := by obtain ⟨k, hk⟩ := ho; omega
  have hlow := RankThree.irrPlus_fixedCodim_gt_eighteen_pslThree
    D.orbitRepresentation D.orbitComponent hI hp hp5 hmO
  have hlowF : 18 < fixedCodim D.orbitRepresentation (generalizedFitting D.orbitActor) :=
    (congrArg (fun X : Subgroup D.orbitActor => 18 < fixedCodim D.orbitRepresentation X)
      (D.orbit_fitting h)).mpr hlow
  apply lt_of_not_ge
  intro hr
  exact not_le_of_gt hlowF
    (RankThree.two_free_fixedCodim_le_eighteen_pslThree D.orbitRepresentation
      (D.orbit_twoCore_eq_bot h) hqF hp ho hmF hr)

theorem linear_three_whole_orbit_excluded (D : ChosenModule T L V)
    (h : Hypothesis1221 κ T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hm : LinearThreeModel p (XiQuotient L))
    (hr : cubicRatio D.orbitRepresentation ≤ 2) : False :=
  not_le_of_gt (linear_three_whole_orbit_cubicRatio_gt_two D h hp ho hp3 hm) hr

end CFSG.Quasithin.Chapter13.Section01
