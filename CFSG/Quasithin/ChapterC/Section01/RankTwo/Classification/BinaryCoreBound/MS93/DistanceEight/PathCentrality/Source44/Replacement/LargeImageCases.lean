module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.PredecessorControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.RegularSource

/-!
# The two remaining large predecessor-image cases of prescribed replacement

The radius image has order two or four. Order four gives switching directly;
order two also does when its join with the local kernel is normalized by the
backward edge kernel. Failure of that normalization forces edge image eight
and predecessor image four or eight. The full predecessor image at j=4 is
now excluded by PredecessorControl: its kernel fixes the original ball center.

The remaining two contracts retain the original critical path, turns,
prescribed edge, the same inverse conjugator, failed span, and fixed-core
induction premise. They request only the backward edge equality needed by
the recurrence, not the stronger normalization of the radius image.
The image-eight contract need only handle j>4.

The two conditional consumers assemble switching and literal prescribed
replacement from these cases. Neither case is asserted from CommonFacts
here; both are still required for unconditional MS93 (4.4.4).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.4), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The unresolved source switching case with predecessor image of order m.
These are proof targets, not additional source assumptions. Both m=4 and
m=8 must be proved before using the resulting replacement unconditionally.
Only the edge equality is requested; radius-image normalization is optional. -/
@[expose] def FailedSpanLargeImageSwitching
    (R : Subgroup M) (geometry : Geometry R) (m : ℕ) : Prop :=
  ∀ {a a'} (p : CriticalPath R geometry a a'), HasTurnConjugators R p →
    ∀ {t}, Adjacent R a t →
      ¬ Z R a' ≤ stabilizer R a ⊓
        normalizer (edgeCommutator R a t : Set (FreeAmalgam R)) →
      ∀ {g}, g ∈ stabilizer R a →
        (edgeCommutator R a (p.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom =
          edgeCommutator R a t →
        (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
          Q R (p.walk.getVert (p.walk.length - 2)) →
        ∀ n : ℕ, 0 < n → 4 * n + 4 ≤ p.walk.length →
          failedSpanCommutator p g = edgeCommutator R
            (p.walk.getVert (p.walk.length - 4 * n))
            (p.walk.getVert (p.walk.length - 4 * n + 1)) →
          failedSpanCommutator p g ≤ fixedCore R
            (p.walk.getVert (p.walk.length - 4 * n + 2)) →
          (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
            (VBall R a (4 * n)) = 2 →
          (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
            (Q R (p.walk.getVert (p.walk.length - 4 * n - 1))) = 8 →
          (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
            (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = m →
          (¬ Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
            normalizer (VBall R a (4 * n) ⊔
              Q R (p.walk.getVert (p.walk.length - 4 * n)) :
                Subgroup (FreeAmalgam R))) →
          (m = 8 → 4 < p.walk.length - 4 * n) →
          failedSpanCommutator p g = edgeCommutator R
            (p.walk.getVert (p.walk.length - 4 * n))
            (p.walk.getVert (p.walk.length - 4 * n - 1))

/-- All other image cases, including the full predecessor at j=4, are
discharged here. The two remaining cases feed the literal recurrence. -/
theorem failedSpanSwitching_of_large_image_cases
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hfour : FailedSpanLargeImageSwitching R geometry 4)
    (height : FailedSpanLargeImageSwitching R geometry 8) :
    FailedSpanSwitching R geometry := by
  intro a a' p hp t ht hne g hg hge hfail
  have seed := RegularSource.terminal_seed common hb p hp ht hne hg hge hfail
  intro n hn hlen hforward hfixed
  have heven : Even (p.walk.length - 4 * n) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [← p.length_eq_b, Nat.even_iff] at he
    rw [Nat.even_iff]
    omega
  obtain ⟨hcomm,hescape,hA⟩ := Iteration.switching_ball_facts common p hg heven
    (by omega) (by omega)
  have hind : p.walk.length - (p.walk.length - 4 * n) = 4 * n := by omega
  rw [hind] at hcomm hescape hA
  have hs : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n - 1)) := by
    apply adjacent_symm R
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 4 * n - 1) (by omega)
    rw [show p.walk.length - 4 * n - 1 + 1 = p.walk.length - 4 * n by omega] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have ht' : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  have hc := (p.vertex_color (by omega)).mpr heven
  have hS : Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      stabilizer R (p.walk.getVert (p.walk.length - 4 * n)) :=
    fun _ hx => hx.2 _ (adjacent_symm R hs)
  have hcard := Iteration.EdgeSwitching.seed_card_four common p seed
  have hKU : failedSpanCommutator p g ≤ U R (p.walk.getVert (p.walk.length - 4 * n)) := by
    rw [hforward]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _ hc ht'
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) _ hc
  rcases actorImage_two_or_four_of_fixed_plane model hKU hcard (hA.trans hS) hescape hcomm
    with htwo | hfourImage
  · by_cases hnorm : Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
        normalizer (VBall R a (4 * n) ⊔ Q R (p.walk.getVert (p.walk.length - 4 * n)) :
          Subgroup (FreeAmalgam R))
    · exact Iteration.EdgeSwitching.edge_switch_of_normalized_radius common hc hs ht'
        hforward hcard hA hescape hcomm hnorm
    obtain ⟨hedge,hprev⟩ := PredecessorKernel.backward_normalization_failure_large_images
      common p hg n hn hlen htwo hnorm
    rcases hprev with hprev | hprev
    · exact hfour p hp ht hne hg hge hfail n hn hlen hforward hfixed htwo hedge hprev
        hnorm (by omega)
    · have hj : 4 < p.walk.length - 4 * n := by
        by_contra! hsmall
        have heq : p.walk.length - 4 * n = 4 := by omega
        exact hnorm (PredecessorControl.radius_normalized_at_four_of_full_predecessor
          p n hn hlen heq (hprev.trans hedge.symm))
      exact height p hp ht hne hg hge hfail n hn hlen hforward hfixed htwo hedge hprev
        hnorm (fun _ => hj)
  · exact edge_switch_of_image_four common model hc hs ht' hforward hcard hA hescape hcomm
      hfourImage

/-- Conditional source consumer retaining the same conjugator in both
prescribed-replacement conclusions. The two large-image cases remain open. -/
theorem prescribedReplacement_of_large_image_cases
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hfour : FailedSpanLargeImageSwitching R geometry 4)
    (height : FailedSpanLargeImageSwitching R geometry 8)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p) :
    PrescribedReplacement R p :=
  SourceCritical.prescribedReplacement common hb
    (failedSpanSwitching_of_large_image_cases common hb hfour height) p hp

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement
