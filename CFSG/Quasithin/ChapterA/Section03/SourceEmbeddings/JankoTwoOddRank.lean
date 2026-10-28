module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LocalRankBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.OddRank
public import Theory.Quasithin.Rank

/-!
# Excluding proper odd-rank-two local components in J₂

Restrict the original Sylow to the containing component. If the smaller
local component is proper, its join with this full Sylow is also proper
by C-component minimality. The checked orders in the exhaustive J₂
Sylow-overgroup cover contradict its p-rank two for p > 3.

Source: Aschbacher–Smith A.3.12(16), pp.47–48, used in 1.3.8, p.513.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- The actual Hall–Janko containing carrier cannot properly contain the
marked local C-component of large odd-prime rank two. -/
theorem eq_of_jankoTwo_containing_component_of_large_odd_rank
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hr : 2 ≤ primeRank p B)
    (e : L ≃* Sporadic.LeechRelated.J2.Carrier) : B = L := by
  apply eq_of_model_proper_local_primeRank_bound T hB hL hBL p hr e
  intro htop S D hd hproper
  have hjoin := local_sup_ne_top_of_ne_top htop S D hd hproper
  exact (primeRank_mono p (show D ≤ D ⊔ (S : Subgroup _) from le_sup_left)).trans
    (Sporadic.LeechRelated.J2.SylowOvergroups.proper_overgroup_primeRank_le_one
      S _ le_sup_right hjoin hp)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
