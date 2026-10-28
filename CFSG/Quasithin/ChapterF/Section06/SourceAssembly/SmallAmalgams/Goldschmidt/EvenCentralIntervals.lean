module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddIntervalReduction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddRadiusOneExclusion
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddRadiusTwoExclusion

/-!
# Even fixed intervals in the large-residual branch

The odd-interval reduction leaves radii one and two. The first forces an
alternating-four local residual; the second contradicts faithful action through
a commutator central at two adjacent vertices. Thus every central involution
on the preferred track has an even fixed interval.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.5)–(6.6), p.398.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- In the large-residual branch, every central involution on the preferred
track has an even fixed interval. Both odd-interval radius cases are excluded
by their actual local residual and commutator conclusions. -/
theorem CubicTreeAction.centralInterval_fixedLength_even
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀u,t.CentralInvolution u→u∉t.fixer)
    (hpreferred : AdjacentInvolutionMovers (RankTwo.graph F) G → t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z) :
    Even (d.fixedRight-d.fixedLeft) := by
  rcases Int.even_or_odd (d.fixedRight-d.fixedLeft) with he | ho
  · exact he
  · have href := Track.hasReflections_of_odd_centralInterval hpreferred d hz ho
    obtain ⟨hw, hm⟩ := h.odd_centralInterval_unit_block_and_equal_margins hs hshort p hp hn t hz d ho
    have hbound := h.odd_centralInterval_rightMargin_le_two hs hshort p hp hn hC hA t
      hfinite hpreferred hz d ho
    have hpos := (h.centralInterval_chiefBounds_of_large_residual hC hA t hz d).2.2.1
    have hcases : d.rightMargin = 1 ∨ d.rightMargin = 2 := by omega
    rcases hcases with hr | hr
    · exact (h.odd_radius_one_impossible hs hshort hC hA t href hz d hw
        (hm.trans hr) hr).elim
    · exact (h.odd_radius_two_impossible hs hshort hC hA t href hz d hw
        (hm.trans hr) hr).elim

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
