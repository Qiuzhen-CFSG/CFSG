module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackRegular
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackGeneration
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.UniversalSetup

/-!
# The strict singularity bound from a maximal regular track segment

If a maximal even regular segment has length `2*m`, the first singularity
index is at most `2*m+1`. Equality would make the shifted segment of the other
parity regular too. Both fixers would normalize the track fixer by their
index-two extensions. Translation supplies this property at every position;
arc generation then puts every vertex stabilizer in the normalizer. The track
fixer would be a normal subgroup of the faithful common overlap, hence trivial.
For a nontrivial track fixer this contradiction gives `s ≤ 2*m-1`.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the equality
exclusion in (5.2), printed p.395. No bound on regularity length is used.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem all_track_segments_le_normalizer_of_two (t : Track (RankTwo.graph F) G) (n : ℕ)
    (h0 : t.segmentFixer 0 n ≤ trackNormalizer t)
    (h1 : t.segmentFixer 1 n ≤ trackNormalizer t) :
    ∀ a : ℤ, t.segmentFixer a n ≤ trackNormalizer t := by
  have hshift (a k : ℤ) (ha : t.segmentFixer a n ≤ trackNormalizer t) :
      t.segmentFixer (a+2*k) n ≤ trackNormalizer t := by
    rw [← t.segmentFixer_map_zpow]
    rintro g ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem (zpow_mem (translation_mem_trackNormalizer t) k) (ha hg))
      (inv_mem (zpow_mem (translation_mem_trackNormalizer t) k))
  intro a
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_index a
  · simpa only [zero_add] using hshift 0 k h0
  · rw [show 2*k+1=1+2*k by omega]
    exact hshift 1 k h1

theorem CubicTreeAction.left_regular_segment_normalizes_fixer (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) (n : ℕ)
    (hr : LeftRegular (A := G) (t.arc a (n+1)))
    (he : t.segmentFixer (a-1) (n+1+1) = trackFixer t) :
    t.segmentFixer a (n+1) ≤ trackNormalizer t := by
  let q := t.arc a (n+1)
  have hrrev := (rightRegular_reverse_iff q).2 hr
  have hi := h.pathStabilizer_snoc_index_two (reverse q) hrrev
    ((forward_reverse_iff_backward q).2 (t.arc_backward a (n+1)))
  have hrev : RankTwo.pathStabilizer F (reverse q) = t.segmentFixer a (n+1) := by
    ext g
    change (∀ v ∈ (reverse q).vertices, g • v = v) ↔ _
    simpa only [vertices_reverse, List.mem_reverse] using t.fixes_arc_iff a (n+1) g
  rw [pathStabilizer_snoc, hrev] at hi
  change (t.segmentFixer a (n+1) ⊓ MulAction.stabilizer G (t.vertex (a-1))).relIndex
    (t.segmentFixer a (n+1)) = 2 at hi
  rw [← t.segmentFixer_prepend, he] at hi
  exact (normal_subgroupOf_iff_le_normalizer (t.fixer_le_segmentFixer a (n+1))).mp
    (normal_of_index_eq_two hi)

theorem CubicTreeAction.last_even_segment_singularity_bound (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false)
    (ht1 : t.vertex 1 = RankTwo.base F true) (hQ : trackFixer t ≠ ⊥)
    {s : ℕ} (hs : 5 ≤ s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) (hv : v.type = false)
    (m : ℕ) (hm : t.segmentFixer 0 (2*m) ≠ trackFixer t)
    (hnext : t.segmentFixer 0 (2*(m+1)) = trackFixer t) : s ≤ 2*m-1 := by
  have hlen := h.last_even_segment_length t hsodd hshort m hnext
  by_contra hbad
  have heq : s=2*m+1 := by obtain ⟨r, hr⟩ := hsodd; omega
  have hext := h.last_even_segment_extensions t (by omega) hsodd hshort p hp hn
    (by rw [ht0]; exact hv.symm) m hnext
  let n := 2*m-1
  have hnm : n+1=2*m := by dsimp [n]; omega
  have hreg : Regular (A := G) (t.arc 0 (n+1)) :=
    h.track_segment_regular_of_extensions t n (by simpa only [hnm] using hm)
      (by simpa only [hnm] using hext.1) (by simpa only [hnm] using hext.2)
  have hN0 := h.regular_segment_normalizes_fixer t 0 n hreg.2
    (by simpa only [hnm] using hext.1)
  have hreg1 : LeftRegular (A := G) (t.arc 1 (n+1)) :=
    (rightRegular_reverse_iff _).1 (hshort _ _ _ (by omega)
      (nonbacktracking_reverse _ (t.arc_nonbacktracking _ _)))
  have hN1 := h.left_regular_segment_normalizes_fixer t 1 n hreg1
    (by simpa only [show (1:ℤ)-1=0 from rfl, hnm] using hext.1)
  have hall := all_track_segments_le_normalizer_of_two t (n+1) hN0 hN1
  have hvertices := h.stabilizers_le_of_track_segments_le t hshort
    (trackNormalizer t) (n+1) (by omega) hall
  have hNtop : trackNormalizer t = ⊤ := by
    apply top_unique
    rw [← h.adjacent_stabilizers_generate (t.adjacent 0)]
    exact sup_le (hvertices 0) (by simpa only [zero_add] using hvertices 1)
  have : (trackFixer t).Normal := normalizer_eq_top_iff.mp hNtop
  have hcore := normal_le_normalCore.mpr (trackFixer_le_baseOverlap t ht0 ht1)
  rw [h.common_core_eq_bot] at hcore
  exact hQ (le_bot_iff.mp hcore)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
