module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleLocalMarking
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleRank
public import CFSG.Quasithin.ChapterA.Section02.RankTwoLocalExclusion

/-!
# Rank-two exclusions for the original nonsingular residual

Apply the rank-two local exclusion to the actual images of L_v and V_v
under K_v -> K_v/Z(K_v). The A₆ two-core quotient and the nontrivial moved
elementary subgroup come from the proved central-quotient marking; the
ambient two-rank comes from the original order-32 module and its fixed line.
No replacement module or full-Sylow premise is introduced.

Source: Aschbacher--Smith, Lemma 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal nonsingular central quotient cannot be any Theorem C rank-two model. -/
theorem SourceHypothesis.nonsingular_not_rankTwo_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    {n : ℕ} :
    ¬ ChapterA.Section02.IsTheoremCRankTwoModel ((Kv (v : G)) ⧸ center (Kv (v : G))) n := by
  obtain ⟨hperf,he,_,hne,hele,_,hn⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let := hperf
  let := hele
  exact ChapterA.Section02.not_rankTwo_of_A6_twoLocal _ _ he hne (IsElementaryAbelian.isPGroup 2 _) hn
    (H.nonsingular_centralQuotient_rank D v hv)
end CFSG.Quasithin.Chapter12.Section06
