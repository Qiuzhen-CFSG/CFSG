module

public import Theory.GroupAction.CubicTree.TrackFixer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackSetup

/-!
# The literal track fixer and its normalizer in the source completion

These are Goldschmidt's groups `G_T` and `N_G(G_T)` in the original coset tree.
The fixer lies in every track vertex stabilizer, is finite, and is normalized
by the chosen translation. A sufficiently long finite segment has exactly
this fixer, supplying the finite-stabilizer input to the maximal subarc of
(5.1). No quotient action or classification is encoded as an assumption.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), Section 5,
printed pp.393--394, with the track convention of (2.9)--(2.11).
-/

@[expose] public section
open Subgroup Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

abbrev trackFixer (t : Track (RankTwo.graph F) G) : Subgroup G := t.fixer

def trackNormalizer (t : Track (RankTwo.graph F) G) : Subgroup G :=
  normalizer (trackFixer t : Set G)

theorem trackFixer_le_stabilizer (t : Track (RankTwo.graph F) G) (i : ℤ) :
    trackFixer t ≤ RankTwo.stabilizer F (t.vertex i) := t.fixer_le_stabilizer i

theorem trackFixer_le_baseOverlap (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false)
    (ht1 : t.vertex 1 = RankTwo.base F true) :
    trackFixer t ≤ F false ⊓ F true := by
  apply le_inf
  · simpa only [ht0, RankTwo.stabilizer, RankTwo.base, stabilizer_base] using
      trackFixer_le_stabilizer t 0
  · simpa only [ht1, RankTwo.stabilizer, RankTwo.base, stabilizer_base] using
      trackFixer_le_stabilizer t 1

theorem CubicTreeAction.finite_trackFixer (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) : Finite (trackFixer t) := by
  let : ∀ i, Finite (F i) := h.finite
  exact t.finite_fixer

theorem translation_mem_trackNormalizer (t : Track (RankTwo.graph F) G) :
    t.translation ∈ trackNormalizer t := t.translation_mem_normalizer_fixer

theorem CubicTreeAction.track_segmentFixer_stabilizes (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) :
    ∃ N : ℕ, ∀ n, N ≤ n → t.segmentFixer a n = trackFixer t := by
  let : ∀ i, Finite (F i) := h.finite
  exact t.segmentFixer_stabilizes (fun i => inferInstance) a

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
