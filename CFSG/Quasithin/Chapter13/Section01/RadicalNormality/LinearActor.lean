module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.ActorBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.LargeDegree
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
/-!
# The fixed-free odd-linear obstruction in the original 13.1.4 branch

The intrinsic embedding theorem leaves either SL₃(p) or PSL₃(p) as the
literal two-core quotient, with p>3. Both alternatives give the same
projective central quotient of the chosen component actor. In the fixed-free
branch its source action is constructed from the original Hypothesis 12.2.1
and Theorem A. Native conjugate generation bounds the binary degree by 18
at cubic ratio at most two, whereas the transitive-plane argument gives
strictly larger degree. Thus the original seed action has ratio greater
than two.

The elimination consumer retains the independent FSU upper bound and the
fixed-free branch explicitly. Their source producers belong to 3.2.5 and
the 12.2.2 branch selection; this is not the full normality theorem 13.1.4.
Source: Aschbacher--Smith, 13.1.4, p.867, via 12.2.2, pp.794--795,
and K.2, p.453. Both central covers and the actual chosen subgroup remain.
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

theorem linear_three_seed_cubicRatio_gt_two (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hm : LinearThreeModel p (XiQuotient L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    2 < cubicRatio D.seedRepresentation := by
  let := h.quasisimple
  have hmC := (linearThree_central_quotient hm).of_mulEquiv
    (D.componentCentralQuotientEquiv h.quasisimple).symm
  have hmF : ClassicalGroup.IsPSL
      ((generalizedFitting D.seedActor) ⧸ center (generalizedFitting D.seedActor)) 3 p :=
    (congrArg (fun X : Subgroup D.seedActor => ClassicalGroup.IsPSL
      (X ⧸ center X) 3 p) (D.seed_fitting h.quasisimple)).mpr hmC
  have ha : SourceAction D.seedRepresentation := D.seed_source_action h hA hc
  apply lt_of_not_ge
  intro hq
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := ho
    omega
  have hlow := RankThree.source_degree_gt_eighteen D.seedRepresentation ha hp
    hp5 hmF
  have hupp := RankThree.source_degree_le_eighteen_pslThree D.seedRepresentation ha hp ho hmF hq
  omega

/-- Literal elimination of the remaining 13.1.4 actor after the independent
source FSU bound has been established on this same chosen action. -/
theorem linear_three_seed_excluded (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : 3 < p)
    (hm : LinearThreeModel p (XiQuotient L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hq : cubicRatio D.seedRepresentation ≤ 2) : False :=
  not_le_of_gt (linear_three_seed_cubicRatio_gt_two D h hA hp ho hp3 hm hc) hq
end CFSG.Quasithin.Chapter13.Section01
