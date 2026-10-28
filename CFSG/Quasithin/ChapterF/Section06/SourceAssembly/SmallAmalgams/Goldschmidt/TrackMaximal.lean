module

public import Theory.GroupAction.CubicTree.TrackArcs
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackNormalizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcIndices

/-!
# Finite maximizing subarcs in the original track

The generic finite-segment fixer is the literal source path stabilizer.
Local transitivity makes the zero-length fixer strictly larger than the
whole track fixer, so the finite descending chain has a last even segment
with this property. This supplies the selected subarc used in (5.1), with
the source action and subgroup inclusions retained.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.1), p.394.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem trackArc_pathStabilizer (t : Track (RankTwo.graph F) G) (a : ℤ) (n : ℕ) :
    RankTwo.pathStabilizer F (t.arc a n) = t.segmentFixer a n := by
  ext g
  exact t.fixes_arc_iff a n g

theorem CubicTreeAction.track_zero_segment_ne_fixer (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) : t.segmentFixer a 0 ≠ trackFixer t := by
  intro he
  have hr := h.zero_arc_regular (t.vertex a)
  obtain ⟨g, hg, hgmove⟩ := hr (t.vertex (a+1)) (t.vertex (a-1)) (t.adjacent a)
    (by
      change (RankTwo.graph F).Adj (t.vertex a) (t.vertex (a-1))
      simpa only [sub_add_cancel] using (t.adjacent (a-1)).symm)
  have hg0 : g ∈ t.segmentFixer a 0 := by
    rw [t.segmentFixer_zero]
    exact hg _ (by simp [BasedWalk.vertices])
  have hgQ : g ∈ t.fixer := by rw [he] at hg0; exact hg0
  have hh := t.injective ((t.mem_fixer.mp hgQ (a+1)).symm.trans hgmove)
  omega

theorem CubicTreeAction.exists_last_even_track_segment (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (a : ℤ) :
    ∃ m : ℕ, t.segmentFixer a (2*m) ≠ trackFixer t ∧
      ∀ k, m < k → t.segmentFixer a (2*k) = trackFixer t := by
  let : ∀ i, Finite (F i) := h.finite
  exact t.exists_last_even_segment (fun i => inferInstance) a
    (h.track_zero_segment_ne_fixer t a)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
