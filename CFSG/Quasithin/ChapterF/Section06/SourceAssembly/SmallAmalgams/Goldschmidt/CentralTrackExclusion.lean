module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackEdgeNormalizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralFixerExclusion
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerSingularity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerThreeClosed
/-!
# The complete central-involution conclusion of Goldschmidt (5.3)

A nontrivial track fixer supplies its actual normalizer candidate, quotient
cubic action and regularity length at least four. The quotient Sylow-three
subgroup is therefore nonnormal. The proved maximal-normalizer and local
pushing-up arguments exclude the intersection with the center of the base
overlap, and the normalizer's action extends this exclusion to every track
edge. A central edge involution thus cannot fix the entire track.

All candidate, quotient and local classification premises are discharged
from the original first-singularity and large-local-residual hypotheses.
Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395; the finite central intervals at the start of Section 6 use
precisely this conclusion.
-/

public section

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup Theory.GroupTheory Theory.GroupAction.CubicTree SimpleGraph
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Goldschmidt (5.3)'s second conclusion for every edge of the original
track, with the candidate, quotient action and three-closed exclusion all
constructed from the first singularity. -/
theorem CubicTreeAction.centralInvolution_not_mem_trackFixer
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G)
    (h0 : t.vertex 0 = RankTwo.base F false) (h1 : t.vertex 1 = RankTwo.base F true)
    {s : ℕ} (hs : 5 ≤ s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) (hv : v.type = false)
    (z : G) (hz : t.CentralInvolution z) : z ∉ t.fixer := by
  classical
  by_cases hQ : t.fixer = ⊥
  · intro hh
    have hz1 : z = 1 := mem_bot.mp (hQ ▸ hh)
    simpa [hz1] using hz.1
  have hc := h.trackFixer_normalizerCandidate t h0 h1 hQ hs hsodd hshort p hp hn hv
  let _ := normalizerQuotientAction h t h0
  obtain ⟨r,hr,_,_,_,hcards⟩ :=
    normalizerQuotient_source h t h0 h1 hQ hs hsodd hshort p hp hn hv
  let P : Sylow 3 (localNormalizer F t.fixer false ⧸
      t.fixer.subgroupOf (localNormalizer F t.fixer false)) := Classical.ofNonempty
  have hP := normalizerQuotient_not_normal_sylow_three h t h0 hc r hr hcards P
  exact hc.centralInvolution_not_mem_fixer_of_base h t h0 h1
    (hc.disjoint_center_overlap_of_large_residual h hC hA P hP) z hz

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
