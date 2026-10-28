module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackRegular
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackNormalizerTransitivity

/-!
# The actual track fixer is a normalizer candidate

For a nontrivial track fixer, select the last even segment with a larger
fixer. Its endpoint regularity and index-two track kernel put the segment
fixer in the track normalizer. The two endpoint actions give transitivity at
the first vertex; composing a suitable local mover with the translation gives
a normalizer element fixing the second vertex and moving the first.

The first right-singular arc is required to start in the first vertex orbit.
This explicit orientation is precisely Goldschmidt's orbit `O`; the separate
reorientation theorem handles the other choice of the original base edge.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.1), p.394,
in the odd singularity branch with index at least five.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem track_normalizerCandidate_of_transitive (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false)
    (ht1 : t.vertex 1 = RankTwo.base F true) (hQ : trackFixer t ≠ ⊥)
    (htrans : ∀ w, (RankTwo.graph F).Adj (t.vertex 0) w →
      ∃ g ∈ trackNormalizer t, g • t.vertex 0 = t.vertex 0 ∧ g • t.vertex 1 = w) :
    NormalizerCandidate F (trackFixer t) := by
  have hbase (i : Bool) {g : G} :
      g • RankTwo.base F i = RankTwo.base F i ↔ g ∈ F i := by
    change g ∈ MulAction.stabilizer G (RankTwo.base F i) ↔ _
    rw [RankTwo.base, stabilizer_base]
  refine ⟨hQ, trackFixer_le_baseOverlap t ht0 ht1, ?_, ?_⟩
  · rw [← normalizer_local_orbit_card (trackFixer t) false]
    have he : MulAction.orbit (localNormalizer F (trackFixer t) false)
        (RankTwo.base F (!false)) = (RankTwo.graph F).neighborSet (t.vertex 0) := by
      ext w
      constructor
      · rintro ⟨g, rfl⟩
        have hg0 : (g:G) • t.vertex 0 = t.vertex 0 := by
          rw [ht0]
          exact (hbase false).2 g.property.2
        have ha := trackGraphAction.map_adj (g:G) (t.adjacent 0)
        change (RankTwo.graph F).Adj (t.vertex 0) ((g:G) • RankTwo.base F true)
        simpa only [zero_add, ht1, hg0] using ha
      · intro hw
        obtain ⟨g, hgN, hg0, hgw⟩ := htrans w hw
        have hgF : g ∈ F false := (hbase false).1 (by simpa only [ht0] using hg0)
        refine ⟨⟨g, hgN, hgF⟩, ?_⟩
        change g • RankTwo.base F true = w
        rwa [ht1] at hgw
    rw [he, h.card_neighbor]
  · have had : (RankTwo.graph F).Adj (t.vertex 0) (t.vertex (-1)) := by
      simpa only [show (-1:ℤ)+1=0 from rfl] using (t.adjacent (-1)).symm
    obtain ⟨x, hxN, hx0, hx1⟩ := htrans (t.vertex (-1)) had
    let g := x⁻¹*t.translation⁻¹
    have hgN : g ∈ trackNormalizer t :=
      mul_mem (inv_mem hxN) (inv_mem (translation_mem_trackNormalizer t))
    have hg1 : g • t.vertex 1 = t.vertex 1 := by
      dsimp only [g]
      rw [mul_smul, t.inverse_translate]
      change x⁻¹ • t.vertex (-1) = t.vertex 1
      rw [← hx1, inv_smul_smul]
    have hg0 : g • t.vertex 0 ≠ t.vertex 0 := by
      intro he
      have he' := congrArg (fun v => x • v) he
      dsimp only [g] at he'
      rw [mul_smul, smul_inv_smul, t.inverse_translate, hx0] at he'
      have := t.injective he'
      omega
    intro hle
    have hgF : g ∈ F true := (hbase true).1 (by simpa only [ht1] using hg1)
    have hgA := (hbase false).2 (hle ⟨hgN, hgF⟩)
    exact hg0 (by simpa only [ht0] using hgA)

theorem CubicTreeAction.trackFixer_normalizerCandidate (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false)
    (ht1 : t.vertex 1 = RankTwo.base F true) (hQ : trackFixer t ≠ ⊥)
    {s : ℕ} (hs : 5 ≤ s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) (hv : v.type = false) :
    NormalizerCandidate F (trackFixer t) := by
  obtain ⟨m, hm, hlarge⟩ := h.exists_last_even_track_segment t 0
  have hnext := hlarge (m+1) (by omega)
  have hlen := h.last_even_segment_length t hsodd hshort m hnext
  have hext := h.last_even_segment_extensions t (by omega) hsodd hshort p hp hn
    (by rw [ht0]; exact hv.symm) m hnext
  let n := 2*m-1
  have hnm : n+1=2*m := by dsimp [n]; omega
  have hreg : Regular (A := G) (t.arc 0 (n+1)) :=
    h.track_segment_regular_of_extensions t n (by simpa only [hnm] using hm)
      (by simpa only [hnm] using hext.1) (by simpa only [hnm] using hext.2)
  have hN := h.regular_segment_normalizes_fixer t 0 n hreg.2
    (by simpa only [hnm] using hext.1)
  exact track_normalizerCandidate_of_transitive h t ht0 ht1 hQ
    (h.regular_track_segment_normalizer_transitive t m n hnm hreg hN)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
