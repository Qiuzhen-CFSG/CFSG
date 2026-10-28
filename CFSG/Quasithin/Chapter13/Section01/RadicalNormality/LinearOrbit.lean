module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.LinearActor
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.OrbitBounds
/-!
# The odd linear-three obstruction on the original full orbit

The source bound in 3.2.5 concerns the T-orbit of the chosen seed. The seed's
irreducible action has binary degree greater than eighteen, so its orbit has
at least that degree. Trivial two-core and the actual quasisimple component
of the orbit actor give the independent upper bound eighteen at cubic ratio
at most two. This proves the contradiction without making the seed
T-invariant or transferring a ratio bound to it.

The fixed-free case is retained explicitly. The genuine earlier source
3.1.8 upper bound on this same orbit action is the remaining premise of the
elimination consumer; this module does not claim the full seven-model list.
Source: Aschbacher--Smith, 13.1.4, p.867, via 12.2.2, pp.794--795,
and the full-orbit bound in 3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
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

theorem linear_three_orbit_cubicRatio_gt_two (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hm : LinearThreeModel p (XiQuotient L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    2 < cubicRatio D.orbitRepresentation := by
  let := h.quasisimple
  have hm0 := linearThree_central_quotient hm
  have hmC := hm0.of_mulEquiv (D.componentCentralQuotientEquiv h.quasisimple).symm
  have hmF : ClassicalGroup.IsPSL
      ((generalizedFitting D.seedActor) ⧸ center (generalizedFitting D.seedActor)) 3 p :=
    (congrArg (fun X : Subgroup D.seedActor => ClassicalGroup.IsPSL
      (X ⧸ center X) 3 p) (D.seed_fitting h.quasisimple)).mpr hmC
  have ha : SourceAction D.seedRepresentation := D.seed_source_action h hA hc
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := ho
    omega
  have hlow := RankThree.source_degree_gt_eighteen D.seedRepresentation ha hp hp5 hmF
  have hle := Submodule.finrank_mono D.seed_le_orbitSpace
  have hmO := hm0.of_mulEquiv (D.orbitCentralQuotientEquiv h).symm
  have hmOF : ClassicalGroup.IsPSL
      ((generalizedFitting D.orbitActor) ⧸ center (generalizedFitting D.orbitActor)) 3 p :=
    (congrArg (fun X : Subgroup D.orbitActor => ClassicalGroup.IsPSL
      (X ⧸ center X) 3 p) (D.orbit_fitting h)).mpr hmO
  have hqF : IsQuasisimple (generalizedFitting D.orbitActor) :=
    (congrArg (fun X : Subgroup D.orbitActor => IsQuasisimple X)
      (D.orbit_fitting h)).mpr (D.orbitComponent_quasisimple h)
  have hfix : fixedSpace D.orbitRepresentation (generalizedFitting D.orbitActor) = ⊥ :=
    (congrArg (fun X : Subgroup D.orbitActor =>
      fixedSpace D.orbitRepresentation X = ⊥) (D.orbit_fitting h)).mpr
        (D.orbit_fixedSpace_eq_bot hc)
  apply lt_of_not_ge
  intro hr
  have hupp := RankThree.two_free_degree_le_eighteen_pslThree D.orbitRepresentation
    (D.orbit_twoCore_eq_bot h) hqF hfix hp ho hmOF hr
  omega

/-- The actual FSU bound on the entire T-orbit excludes the odd linear branch. -/
theorem linear_three_orbit_excluded (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hm : LinearThreeModel p (XiQuotient L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hq : cubicRatio D.orbitRepresentation ≤ 2) : False :=
  not_le_of_gt (linear_three_orbit_cubicRatio_gt_two D h hA hp ho hp3 hm hc) hq
end CFSG.Quasithin.Chapter13.Section01
