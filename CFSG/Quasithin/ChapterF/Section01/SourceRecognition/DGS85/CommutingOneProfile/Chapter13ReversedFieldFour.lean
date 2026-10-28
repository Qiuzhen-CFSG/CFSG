module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReversedElementaryConsumers
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalEscape

/-!
# The complete commuting distance-one branch at the original A5 factor

The original Chapter 13 context supplies the PSL2(4) marking on its same
chosen L. An attained critical edge transports to one of the two base-edge
orientations. The alpha orientation contradicts the proved square-field
relation and nonsolvability. In the beta orientation, that original linear
marking supplies the elementary quotient and the constructed reverse U4
comparison. Chapter 15 then restores the same original pair and full Borel.

No critical orientation, local catalogue, reflection, exchange or finite
quotient is supplied. Other critical distances and the noncommuting branch
remain with the original normalized-recognition assembly.
Source: Aschbacher--Smith 13.6.27, pp.934--935, and 5.2.4--6, pp.649--651;
DGS, Groups and Graphs (1985), (11.7)--(11.8), pp.174--177, and (15.2).
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Subgroup Theory.GroupTheory
open Components Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
open Chapter12.Section02 Chapter6.Source.RankOneGeneric
open ChapterF.Source.DGS85 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H A B R : Subgroup G}

/-- The original A5 chosen-factor consumer for the entire commuting
b=1 branch, retaining its selected perfect partner and both original
inclusion maps, without a specified critical orientation. -/
theorem original_comparison_of_commuting_one
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (p : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans e.symm⟩
  exact d.chosen.rankOne_comparison_of_commuting_one_small_degree_source
    (original_hypothesis1223 d).toHypothesis1221 hmany (by decide) hpsl hH p hp hb hcomm (by decide)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
