module

public import Theory.GroupAction.CubicTree.TrackArcTransport
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackMaximal
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcGeneration

/-!
# Generation by all translates of a short track segment fixer

Adjacent short segment fixers generate their overlap fixer by the proved
source arc-generation theorem. Repeatedly shortening the intervals shows
that a subgroup containing every translate along the track of one short
segment fixer contains every track vertex stabilizer. This is the generation
step excluding equality in the singularity comparison of (5.2).

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.13), p.384,
and its application in (5.2), p.395.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem track_arcIntervalStabilizer (t : Track (RankTwo.graph F) G)
    (a : ℤ) (n j i : ℕ) (hji : j ≤ i) (hi : i ≤ n) :
    arcIntervalStabilizer (t.arc a n).toWalk j i = t.segmentFixer (a+j) (i-j) := by
  ext g
  change (∀ k, j ≤ k → k ≤ i → g • (t.arc a n).toWalk.getVert k =
    (t.arc a n).toWalk.getVert k) ↔ _
  rw [t.mem_segmentFixer]
  constructor
  · intro hg z haz hzi
    have he : a+((z-a).toNat:ℤ)=z := by omega
    have hk : (z-a).toNat ≤ n := by omega
    have hz := hg (z-a).toNat (by omega) (by omega)
    simpa only [t.arc_getVert _ _ _ hk, he] using hz
  · intro hg k hjk hki
    rw [t.arc_getVert _ _ _ (hki.trans hi)]
    exact hg (a+k) (by omega) (by omega)

theorem CubicTreeAction.adjacent_track_segments_generate (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {s n : ℕ}
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hn : n+2 ≤ s) (a : ℤ) :
    t.segmentFixer a (n+1) ⊔ t.segmentFixer (a+1) (n+1) =
      t.segmentFixer (a+1) n := by
  have he := h.arc_stabilizers_generate_overlap hshort hn (t.arc a (n+2))
    (t.arc_nonbacktracking _ _) (i := n+1) (j := 1) (by omega) (by omega)
  rw [track_arcIntervalStabilizer _ _ _ _ _ (by omega) (by omega),
    track_arcIntervalStabilizer _ _ _ _ _ (by omega) (by omega),
    track_arcIntervalStabilizer _ _ _ _ _ (by omega) (by omega)] at he
  simpa only [Nat.cast_zero, add_zero, Nat.sub_zero, Nat.cast_one,
    Nat.add_sub_cancel, show n+2-1=n+1 by omega] using he

theorem CubicTreeAction.stabilizers_le_of_track_segments_le (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {s : ℕ}
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (N : Subgroup G) (n : ℕ) (hn : n < s)
    (hall : ∀ a : ℤ, t.segmentFixer a n ≤ N) :
    ∀ a : ℤ, RankTwo.stabilizer F (t.vertex a) ≤ N := by
  induction n with
  | zero => intro a; simpa only [t.segmentFixer_zero] using hall a
  | succ n ih =>
    apply ih (by omega)
    intro a
    have he := h.adjacent_track_segments_generate t hshort (n := n) (by omega) (a-1)
    rw [sub_add_cancel] at he
    rw [← he]
    exact sup_le (hall (a-1)) (hall a)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
