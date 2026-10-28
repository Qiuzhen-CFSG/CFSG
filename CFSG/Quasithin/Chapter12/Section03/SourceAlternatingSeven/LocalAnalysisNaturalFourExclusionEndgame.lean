module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionResiduals
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer

/-!
# The block endgame for the published central-line residual interface

The literal residual here is the solvable residual of O²(C_{N(V)}(z)).
Its normalization by M_z identifies its conjugate span with itself.
The proved C.2.12 block and Frattini theorem then gives N_{G_z}(K_z)=M_z.
Consequently relative normality in G_z contradicts the original escaping
point centralizer.

This completes the conditional endgame with FourResidualData and relative
normality as explicit inputs. Their discharge remains with
qt-d-1233-natural-coordinates. The separate C_L(z)∞ route and its residual
conventions are unchanged.
Source: Aschbacher–Smith, Lemma 12.3.3, printed p.808; C.2.12, p.148.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- C.2.12's block and Frattini argument controls the normalizer of the
literal solvable residual of O²(C_{N(V)}(z)). -/
theorem four_pointPerfect_normalizer_of_residualData
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) (D : S.FourResidualData z) :
    S.fourPointCentralizer z ⊓ normalizer (S.fourPointPerfect z : Set G) =
      S.fourPointLocal z := by
  have he : conjugateSpanBy (S.fourPointPerfect z) (S.fourPointLocal z) =
      S.fourPointPerfect z :=
    le_antisymm (conjugateSpanBy_le le_rfl
      (S.four_pointLocal_normalizes_perfect structural hz hz1)) (le_conjugateSpanBy _ _)
  have h := D.pushingUp.normalizer_span_eq
  rwa [he] at h

/-- The exact conditional block-endgame contract: relative normality of
the original residual contradicts the original point-centralizer escape. -/
theorem four_false_of_residual_normality
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) (D : S.FourResidualData z)
    (hn : S.fourPointCentralizer z ≤ normalizer (S.fourPointPerfect z : Set G)) : False := by
  have he := S.four_pointPerfect_normalizer_of_residualData structural hz hz1 D
  rw [inf_eq_left.mpr hn] at he
  exact S.four_all_pointCentralizers_escape escape e hd hz hz1 (he.le.trans inf_le_left)

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
