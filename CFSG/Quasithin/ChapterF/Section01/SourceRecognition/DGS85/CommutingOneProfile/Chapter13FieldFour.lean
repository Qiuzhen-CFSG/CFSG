module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FieldDegreeConsumers
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalEscape

/-!
# The commuting distance-one exclusion at the original A5 alpha factor

The original Chapter 13 context identifies its same L/O2(L) with A5, hence
PSL2(4). Its chosen module supplies the full KnownSimple Chapter 12 input.
For every prepared perfect right factor R, the commuting distance-one
source theorem would force the original left exponent two to be at least
four. Both elementary and nonelementary beta quotients are thereby excluded.

The full original Borel, selected R and critical alpha orientation are
retained. This removes that branch from the original normalized recognition
problem; it does not choose the critical pair or exclude its reverse
orientation, and it does not assert the whole terminal classification.
Source: Aschbacher--Smith 13.6.27, pp.934--935, and 5.2.4--6, pp.649--651;
DGS, Groups and Graphs (1985), (11.7)--(11.8), pp.174--177.
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

/-- At the original A5 chosen factor, both elementary and nonelementary
commuting source branches are impossible when that factor is the critical
alpha endpoint. The selected right factor and complete original Borel are
unchanged; no reflection, finite quotient or local catalogue is supplied. -/
theorem original_not_commuting_one_at_alpha
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (p : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false)
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true))
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥) : False := by
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans e.symm⟩
  exact d.chosen.rankOne_not_commuting_one_of_small_degree
    (original_hypothesis1223 d).toHypothesis1221 hmany (by decide) hpsl hH p hp hc hb hcomm (by decide)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
