module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackCandidate
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackSingularityBound
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerTrackArcs
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerRegularity

/-!
# The source normalizer quotient and the singularity comparison

Starting with the original cubic tree action and a nontrivial track fixer, the
proved maximal-segment argument supplies the normalizer candidate. The actual
distance-two component and faithful quotient therefore have a regular arc
length. A maximal original segment of length `2*m` has `s ≤ 2*m-1`, while its
nontrivial quotient fixer implies `m < r` for any free arc length `r` of the
quotient. Thus `s ≤ 2*r-3`.

The final theorem packages the exact quotient action, regularity predicates,
and stabilizer cardinality needed in the semilocal centralizer argument. For
`s ≥ 5`, it proves `r ≥ 4`. Every graph and quotient premise is produced from
the original source hypotheses; no general upper bound on regularity is used.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.1)--(5.2),
printed pp.394--395, in the odd singularity branch used by (5.3).
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem normalizerQuotient_singularity_bound (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false)
    (ht1 : t.vertex 1 = RankTwo.base F true) (hQ : trackFixer t ≠ ⊥)
    {s : ℕ} (hs : 5 ≤ s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) (hv : v.type = false)
    (r : ℕ) :
    letI := normalizerQuotientAction h t ht0
    WeissEven.ArcFree (Γ := (normalizerComponent F (trackFixer t)).toSimpleGraph)
      (G := normalizerComponentQuotient F (trackFixer t)) r → s ≤ 2*r-3 := by
  let := normalizerQuotientAction h t ht0
  intro hfree
  have hcandidate := h.trackFixer_normalizerCandidate t ht0 ht1 hQ hs hsodd hshort p hp hn hv
  obtain ⟨m, hm, hlarge⟩ := h.exists_last_even_track_segment t 0
  have hnext := hlarge (m+1) (by omega)
  have hbound := h.last_even_segment_singularity_bound t ht0 ht1 hQ hs hsodd hshort
    p hp hn hv m hm hnext
  have hext := h.last_even_segment_extensions t (by omega) hsodd hshort p hp hn
    (by rw [ht0]; exact hv.symm) m hnext
  let n := 2*m-1
  have hnm : n+1=2*m := by dsimp [n]; omega
  have hreg : Regular (A := G) (t.arc 0 (n+1)) :=
    h.track_segment_regular_of_extensions t n (by simpa only [hnm] using hm)
      (by simpa only [hnm] using hext.1) (by simpa only [hnm] using hext.2)
  have hN : t.segmentFixer 0 (2*m) ≤ trackNormalizer t := by
    simpa only [hnm] using h.regular_segment_normalizes_fixer t 0 n hreg.2
      (by simpa only [hnm] using hext.1)
  have hmr := normalizerTrack_length_lt_regularity h t ht0 hcandidate m r hm hN hfree
  omega

theorem normalizerQuotient_source (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G)
    (ht0 : t.vertex 0 = RankTwo.base F false)
    (ht1 : t.vertex 1 = RankTwo.base F true) (hQ : trackFixer t ≠ ⊥)
    {s : ℕ} (hs : 5 ≤ s) (hsodd : Odd s)
    (hshort : ∀ k v (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p) (hv : v.type = false) :
    letI := normalizerQuotientAction h t ht0
    ∃ r : ℕ, 4 ≤ r ∧ s ≤ 2*r-3 ∧
      (∀ k (x : normalizerComponent F (trackFixer t))
        (q : BasedWalk (normalizerComponent F (trackFixer t)).toSimpleGraph k x),
        k < r → q.Nonbacktracking →
          RightRegular (A := normalizerComponentQuotient F (trackFixer t)) q) ∧
      WeissEven.ArcFree (Γ := (normalizerComponent F (trackFixer t)).toSimpleGraph)
        (G := normalizerComponentQuotient F (trackFixer t)) r ∧
      ∀ x : normalizerComponent F (trackFixer t),
        Nat.card (MulAction.stabilizer (normalizerComponentQuotient F (trackFixer t)) x) =
          3*2^(r-1) := by
  let := normalizerQuotientAction h t ht0
  have hcandidate := h.trackFixer_normalizerCandidate t ht0 ht1 hQ hs hsodd hshort p hp hn hv
  obtain ⟨r, hrpos, hrshort, hrfree, hrcard⟩ := normalizerQuotient_regularity h t ht0 hcandidate
  have hbound := normalizerQuotient_singularity_bound h t ht0 ht1 hQ hs hsodd hshort
    p hp hn hv r hrfree
  exact ⟨r, by omega, hbound, hrshort, hrfree, hrcard⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
