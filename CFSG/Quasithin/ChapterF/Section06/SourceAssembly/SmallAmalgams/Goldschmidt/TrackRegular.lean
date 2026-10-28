module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackMaximal
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSingularity
public import Theory.GroupAction.CubicTree.TrackTranslation

/-!
# Regularity of the last even track segment

Fix the orientation of a first right-singular arc. The last even segment whose
fixer is larger than the track fixer has length at least the singularity index
minus one. Each odd one-step extension is singular at the corresponding end;
its fixer therefore already equals the fixer of the following even extension,
which is the track fixer. The original segment is regular at both ends, and
its fixer normalizes the track fixer because the latter has index two.

These arguments use the actual finite track filtration and the established
arc singularity and index lemmas. The orientation hypothesis remains explicit.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.1), p.394.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.track_segment_ne_fixer_of_regular (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) (n : ℕ)
    (hreg : RightRegular (A := G) (t.arc a n)) : t.segmentFixer a n ≠ trackFixer t := by
  cases n with
  | zero => exact h.track_zero_segment_ne_fixer t a
  | succ n =>
    intro he
    have hi := h.pathStabilizer_snoc_index_two (t.arc a (n+1)) hreg
      (t.arc_forward a (n+1))
    rw [pathStabilizer_snoc, trackArc_pathStabilizer] at hi
    have hnext : t.segmentFixer a (n+1) ⊓
        RankTwo.stabilizer F (t.vertex (a+(n+1:ℕ)+1)) = trackFixer t := by
      rw [he]
      exact inf_eq_left.mpr (trackFixer_le_stabilizer t _)
    rw [hnext, he, Subgroup.relIndex_self] at hi
    omega

theorem CubicTreeAction.left_nonregular_of_opposite_start (h : CubicTreeAction F)
    {s : ℕ} (hs : 0 < s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {n : ℕ} (hsn : s ≤ n) {w : RankTwo.Vertex F}
    (q : BasedWalk (RankTwo.graph F) n w) (hq : q.Nonbacktracking)
    (ht : w.type ≠ v.type) : ¬ LeftRegular (A := G) q := by
  intro hr
  exact h.left_nonregular_opposite hs hshort p hp hn (q.take s hsn)
    (BasedWalk.nonbacktracking_take hsn q hq) ht (leftRegular_take q hs hsn hr)

theorem CubicTreeAction.right_nonregular_of_opposite_endpoint (h : CubicTreeAction F)
    {s : ℕ} (hs : 0 < s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    {n : ℕ} (hsn : s ≤ n) {w : RankTwo.Vertex F}
    (q : BasedWalk (RankTwo.graph F) n w) (hq : q.Nonbacktracking)
    (ht : q.endpoint.type ≠ v.type) : ¬ RightRegular (A := G) q := by
  intro hr
  exact h.left_nonregular_of_opposite_start hs hshort p hp hn hsn (reverse q)
    (nonbacktracking_reverse q hq) ht ((leftRegular_reverse_iff q).2 hr)

theorem track_even_type (t : Track (RankTwo.graph F) G) (k : ℤ) :
    (t.vertex (2*k)).type = (t.vertex 0).type := by
  have he := t.zpow_translate k 0
  rw [zero_add] at he
  rw [← he]
  rfl

theorem track_odd_type (t : Track (RankTwo.graph F) G) (k : ℤ) :
    (t.vertex (2*k+1)).type = (t.vertex 1).type := by
  have he := t.zpow_translate k 1
  rw [show 1+2*k = 2*k+1 by omega] at he
  rw [← he]
  rfl

theorem CubicTreeAction.last_even_segment_length (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {s : ℕ} (hs : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (m : ℕ) (hm : t.segmentFixer 0 (2*(m+1)) = trackFixer t) : s ≤ 2*m+1 := by
  by_contra hn
  have hlt : 2*(m+1) < s := by obtain ⟨r, hr⟩ := hs; omega
  exact h.track_segment_ne_fixer_of_regular t 0 (2*(m+1))
    (hshort _ _ _ hlt (t.arc_nonbacktracking _ _)) hm

theorem CubicTreeAction.segment_succ_eq_of_not_rightRegular (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) (n : ℕ)
    (hn : ¬ RightRegular (A := G) (t.arc a (n+1))) :
    t.segmentFixer a (n+1+1) = t.segmentFixer a (n+1) := by
  rw [t.segmentFixer_succ]
  apply inf_eq_left.mpr
  intro g hg
  exact fixes_forward_of_not_rightRegular trackGraphAction _ (h.card_neighbor _)
    hn g ((t.fixes_arc_iff _ _ _).2 hg) (t.arc_forward _ _)

theorem CubicTreeAction.segment_prepend_eq_of_not_leftRegular (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) (n : ℕ)
    (hn : ¬ LeftRegular (A := G) (t.arc a (n+1))) :
    t.segmentFixer (a-1) (n+1+1) = t.segmentFixer a (n+1) := by
  rw [t.segmentFixer_prepend]
  apply inf_eq_left.mpr
  intro g hg
  exact fixes_backward_of_not_leftRegular trackGraphAction _ (h.card_neighbor _)
    hn g ((t.fixes_arc_iff _ _ _).2 hg) (t.arc_backward _ _)

theorem track_segment_two_left_eq_fixer (t : Track (RankTwo.graph F) G) (n : ℕ)
    (hn : t.segmentFixer 0 n = trackFixer t) :
    t.segmentFixer (-2) n = trackFixer t := by
  apply Subgroup.map_injective (f := (MulAut.conj t.translation).toMonoidHom)
    (MulAut.conj t.translation).injective
  rw [t.segmentFixer_translate]
  have hnQ := (mem_normalizer_iff_map_conj_eq).mp t.translation_mem_normalizer_fixer
  rw [show (-2:ℤ)+2=0 from rfl, hn]
  exact hnQ.symm

theorem CubicTreeAction.last_even_segment_extensions (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {s : ℕ} (hs : 0 < s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (htype : (t.vertex 0).type = v.type)
    (m : ℕ) (hm : t.segmentFixer 0 (2*(m+1)) = trackFixer t) :
    t.segmentFixer 0 (2*m+1) = trackFixer t ∧
      t.segmentFixer (-1) (2*m+1) = trackFixer t := by
  have hlen := h.last_even_segment_length t hsodd hshort m hm
  have hop : (t.vertex 1).type ≠ v.type := by
    have ha := (t.adjacent 0).1
    simpa only [zero_add, htype] using ha.symm
  have hf : ¬ RightRegular (A := G) (t.arc 0 (2*m+1)) := by
    apply h.right_nonregular_of_opposite_endpoint hs hshort p hp hn hlen _
      (t.arc_nonbacktracking _ _)
    rw [t.arc_endpoint]
    simpa only [zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      track_odd_type] using hop
  have hl : ¬ LeftRegular (A := G) (t.arc (-1) (2*m+1)) := by
    apply h.left_nonregular_of_opposite_start hs hshort p hp hn hlen _
      (t.arc_nonbacktracking _ _)
    have ht := track_odd_type t (-1)
    norm_num at ht
    exact ht ▸ hop
  have hef := h.segment_succ_eq_of_not_rightRegular t 0 (2*m) hf
  have hel := h.segment_prepend_eq_of_not_leftRegular t (-1) (2*m) hl
  constructor
  · rw [← hef]
    simpa only [show 2*m+1+1=2*(m+1) by omega] using hm
  · rw [← hel]
    simpa only [show (-1:ℤ)-1 = -2 from rfl, show 2*m+1+1=2*(m+1) by omega] using
      track_segment_two_left_eq_fixer t (2*(m+1)) hm

theorem CubicTreeAction.track_segment_regular_of_extensions (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (n : ℕ)
    (hne : t.segmentFixer 0 (n+1) ≠ trackFixer t)
    (hr : t.segmentFixer 0 (n+1+1) = trackFixer t)
    (hl : t.segmentFixer (-1) (n+1+1) = trackFixer t) :
    Regular (A := G) (t.arc 0 (n+1)) := by
  have hnot : ¬ t.segmentFixer 0 (n+1) ≤ trackFixer t :=
    fun hle => hne (le_antisymm hle (t.fixer_le_segmentFixer _ _))
  obtain ⟨g, hg, hgQ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hfix := (t.fixes_arc_iff _ _ _).2 hg
  have hmover : g • t.vertex (0+(n+1:ℕ)+1) ≠ t.vertex (0+(n+1:ℕ)+1) := by
    intro he
    apply hgQ
    rw [← hr, t.segmentFixer_succ]
    exact ⟨hg, he⟩
  have hmovel : g • t.vertex (0-1) ≠ t.vertex (0-1) := by
    intro he
    apply hgQ
    rw [← hl]
    change g ∈ t.segmentFixer (0-1) (n+1+1)
    rw [t.segmentFixer_prepend]
    exact ⟨hg, he⟩
  refine ⟨?_, rightRegular_of_moved_forward trackGraphAction _ (h.card_neighbor _)
    g hfix (t.arc_forward _ _) hmover⟩
  apply (rightRegular_reverse_iff _).1
  apply rightRegular_of_moved_forward trackGraphAction _ (h.card_neighbor _) g
    (by simpa only [vertices_reverse, List.mem_reverse] using hfix)
    ((forward_reverse_iff_backward _).2 (t.arc_backward _ _)) hmovel

theorem CubicTreeAction.regular_segment_normalizes_fixer (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) (n : ℕ)
    (hr : RightRegular (A := G) (t.arc a (n+1)))
    (he : t.segmentFixer a (n+1+1) = trackFixer t) :
    t.segmentFixer a (n+1) ≤ trackNormalizer t := by
  have hi := h.pathStabilizer_snoc_index_two _ hr (t.arc_forward a (n+1))
  rw [pathStabilizer_snoc, trackArc_pathStabilizer] at hi
  change (t.segmentFixer a (n+1) ⊓
    MulAction.stabilizer G (t.vertex (a+(n+1:ℕ)+1))).relIndex
      (t.segmentFixer a (n+1)) = 2 at hi
  rw [← t.segmentFixer_succ, he] at hi
  exact (normal_subgroupOf_iff_le_normalizer (t.fixer_le_segmentFixer a (n+1))).mp
    (normal_of_index_eq_two hi)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
