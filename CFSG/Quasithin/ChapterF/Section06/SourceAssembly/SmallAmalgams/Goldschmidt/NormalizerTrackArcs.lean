module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerGeometry
public import Theory.GroupAction.CubicTree.TrackArcs
public import Theory.GroupAction.CubicTree.WeissEven

/-!
# The even track arc in the faithful normalizer quotient

Every second vertex of the original track forms a nonbacktracking arc in the
normalizer's cubic component. An element of a segment fixer that normalizes
the track fixer acts on this component, and remains nontrivial in the quotient
precisely when it is outside the track fixer. It fixes both ends of the
corresponding even track arc and therefore the entire arc. A free action on
arcs of length `r` forces the half-length of this segment to be less than `r`.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.2), p.394.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

noncomputable def normalizerTrackArc (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (m : ℕ) : BasedWalk (normalizerComponent F (trackFixer t)).toSimpleGraph m
      (trackEvenComponentVertex h t ht0 0) :=
  sequenceWalk (trackEvenComponentVertex h t ht0)
    (trackEvenComponentVertex_adj h t ht0) 0 m

theorem normalizerTrackArc_endpoint (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (m : ℕ) : (normalizerTrackArc h t ht0 m).endpoint =
      trackEvenComponentVertex h t ht0 m := by
  exact (sequenceWalk_endpoint _ _ _ _).trans (congrArg _ (zero_add _))

theorem normalizerTrackArc_nonbacktracking (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (m : ℕ) : (normalizerTrackArc h t ht0 m).Nonbacktracking := by
  apply sequenceWalk_nonbacktracking
  intro i he
  have he' := congrArg (fun x : normalizerComponent F (trackFixer t) => x.val.val) he
  have he'' := t.injective he'
  omega

theorem normalizerTrack_length_lt_regularity (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (ht0 : t.vertex 0 = RankTwo.base F false)
    (hQ : NormalizerCandidate F (trackFixer t)) (m r : ℕ)
    (hne : t.segmentFixer 0 (2*m) ≠ trackFixer t)
    (hN : t.segmentFixer 0 (2*m) ≤ trackNormalizer t) :
    letI := normalizerQuotientAction h t ht0
    WeissEven.ArcFree (Γ := (normalizerComponent F (trackFixer t)).toSimpleGraph)
      (G := normalizerComponentQuotient F (trackFixer t)) r → m < r := by
  let := normalizerQuotientAction h t ht0
  intro hfree
  by_contra hbad
  have hrm : r ≤ m := by omega
  have hnot : ¬ t.segmentFixer 0 (2*m) ≤ trackFixer t :=
    fun hle => hne (le_antisymm hle (t.fixer_le_segmentFixer _ _))
  obtain ⟨g, hg, hgQ⟩ := SetLike.not_le_iff_exists.mp hnot
  let gL : normalizer (trackFixer t : Set G) := ⟨g, hN hg⟩
  have hg0 : g • t.vertex 0 = t.vertex 0 :=
    t.mem_segmentFixer.mp hg 0 le_rfl (by omega)
  have hgC : gL ∈ normalizerComponentGroup F (trackFixer t) := by
    apply ComponentAction.stabilizer_le (normalizerComponent F (trackFixer t))
      (normalizerGraphAction F (trackFixer t)) (trackEvenComponentVertex h t ht0 0)
    apply Subtype.ext
    change g • t.vertex (2*0) = t.vertex (2*0)
    simpa only [mul_zero] using hg0
  let gC : normalizerComponentGroup F (trackFixer t) := ⟨gL, hgC⟩
  let a : normalizerComponentQuotient F (trackFixer t) :=
    QuotientGroup.mk' (normalizerComponentKernel F (trackFixer t)) gC
  have ha : a ≠ 1 := by
    intro he
    exact hgQ ((QuotientGroup.eq_one_iff gC).mp he)
  let q := normalizerTrackArc h t ht0 m
  have hq := normalizerTrackArc_nonbacktracking h t ht0 m
  obtain ⟨htree, _, _, hact, _⟩ := normalizerQuotient_geometry h t ht0 hQ
  have hfix : ∀ z ∈ q.vertices, a • z = z := by
    apply BasedWalk.fixes_short_walk (N := 2*m)
      (fun _ c hc => (htree.isAcyclic c hc).elim) q hq le_rfl (actionIso hact a)
    · apply Subtype.ext
      apply Subtype.ext
      change g • t.vertex (2*0) = t.vertex (2*0)
      simpa only [mul_zero] using hg0
    · change a • q.endpoint = q.endpoint
      rw [normalizerTrackArc_endpoint]
      apply Subtype.ext
      apply Subtype.ext
      change g • t.vertex (2*(m:ℤ)) = t.vertex (2*(m:ℤ))
      exact t.mem_segmentFixer.mp hg _ (by omega) (by omega)
  apply ha
  apply hfree _ (q.take r hrm) (BasedWalk.nonbacktracking_take hrm q hq) a
  intro z hz
  apply hfix z
  rw [BasedWalk.vertices_take] at hz
  exact List.mem_of_mem_take hz

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
