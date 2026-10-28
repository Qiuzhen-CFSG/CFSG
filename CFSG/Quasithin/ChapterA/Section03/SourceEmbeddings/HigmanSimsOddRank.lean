module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LocalRankBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.OddRank

/-!
# The Higman–Sims containing-component exclusion

Restrict the original full Sylow and transport the smaller local component.
Its proper Sylow join has large odd-prime rank at most one by the literal
HS overgroup cover, contradicting the marked rank two.

Source: Aschbacher–Smith A.3.12(18), pp.47–48, used in 1.3.8, p.513.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- No proper marked local C-component of large odd-prime rank two occurs
in the actual Higman–Sims carrier. -/
theorem eq_of_higmanSims_containing_component_of_large_odd_rank
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p) (hr : 2 ≤ primeRank p B)
    (e : L ≃* Sporadic.LeechRelated.HS.Carrier) : B = L := by
  apply eq_of_model_proper_local_primeRank_bound T hB hL hBL p hr e
  intro htop S D hd hproper
  have hjoin := local_sup_ne_top_of_ne_top htop S D hd hproper
  exact (primeRank_mono p (show D ≤ D ⊔ (S : Subgroup _) from le_sup_left)).trans
    (Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_primeRank_le_one
      S _ le_sup_right hjoin hp ho)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
