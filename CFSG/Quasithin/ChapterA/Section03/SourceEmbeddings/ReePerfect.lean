module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LocalRankBound
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import BenderSuzuki.SE.Section11Lemma114Models

/-!
# Odd-rank-two local components in the Ree containing carrier

Every proper local component in a full Sylow overgroup is one of the two
actual parabolic residuals. Their two-core quotients are PSL₂(q) and Sz(q),
both with cyclic odd Sylow subgroups. Thus neither residual can contain the
marked odd-prime rank two. Restriction retains the original full Sylow
intersection and transports the actual subgroup, with no quasisimplicity
assumption on the smaller component.

Source: Aschbacher–Smith A.3.12(2–3), pp.47–48, used in 1.3.8, p.513.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

/-- Both genuine Ree local factors have odd-prime rank at most one. -/
theorem ree_localFactor_odd_primeRank_le_one (m : ℕ) (s : ReeF4.LargeLocalSeeds.Side)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (ReeF4.Parabolics.localFactor m s) ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho
    (pCore 2 (ReeF4.Parabolics.localFactor m s)) pCore_isPGroup]
  cases s with
  | linear =>
    rw [primeRank_equiv p (ReeF4.Parabolics.linearLocalQuotientEquiv m),
      ← primeRank_equiv p
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := ReeF4.CoefficientField m))]
    exact Matrix.SL2.binary_odd_primeRank_le_one ho
  | suzuki =>
    rw [primeRank_equiv p (ReeF4.Parabolics.suzukiLocalQuotientEquiv m)]
    let S : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := default
    apply S.primeRank_le_one_of_isCyclic
    exact BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic m p Fact.out
      (by rintro rfl; norm_num at ho) S

/-- Odd rank excludes every proper smaller local C-component in a genuine
Ree F₄ containing component. -/
theorem eq_of_ree_containing_component_of_odd_rank
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p B)
    {m : ℕ} (hm : 1 ≤ m) (e : L ≃* ReeF4.Model m) : B = L := by
  apply eq_of_model_proper_local_primeRank_bound T hB hL hBL p hr e
  intro htop S D hd hproper
  obtain ⟨g,s,he⟩ := ReeLocal.local_placement hm htop S D hd hproper
  have hb := ree_localFactor_odd_primeRank_le_one m s ho
  rw [← he] at hb
  exact (primeRank_equiv p ((MulAut.conj g).subgroupMap D)).trans_le hb

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
