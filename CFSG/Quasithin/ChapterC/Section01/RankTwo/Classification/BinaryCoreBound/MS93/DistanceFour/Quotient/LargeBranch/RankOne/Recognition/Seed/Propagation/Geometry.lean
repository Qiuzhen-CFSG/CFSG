module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Actors

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Geometry.TripleProduct

/-!
# Propagation by the full incident-flag parabolics

Write P₁ and P₂ for the actual full parabolics of the seed frame, X for
the seed preimage, and T = Z_alpha Z_c for the midpoint line preimage.
Local fixation gives P₁ ≤ N(T), while the seed gives P₂ ≤ N(X) and T ≤ X.
The finite flag factorization M = P₁ P₂ P₁ therefore identifies the full
midpoint orbit span with the P₁-conjugate span of X.

Inside V_alpha, centralizing Z_c is equivalent to centralizing T, since
Z_alpha centralizes V_alpha. The distance-two centralizer identity identifies
this subgroup with V_alpha ∩ Q_c. It is normalized by P₁ and contains X,
so it contains the full midpoint orbit span.

This is an alternative ambient propagation argument for MS93 (1993),
(4.6.12)(3), printed pp.910–911, using the actual flag geometry defined on
p.905. It supplies the same V₀ ≤ Q_c conclusion without the printed
base-core generation formula disproved in Actors, or the unproved proposed
replacement using Q_delta4. No recognition, whole-span containment, or
core-generation assertion is an extra premise. The original amalgam is
never assumed finite. The parent retains marked cyclic recognition and
final assembly of the source clause.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The binary flag factorization lifts through the specified quotient to M.
The quotient kernel is absorbed into the last full parabolic. -/
theorem Frame.triple_product (f : Frame source) (m : M) :
    ∃ a ∈ f.parabolic false, ∃ b ∈ f.parabolic true,
      ∃ c ∈ f.parabolic false, m = a * b * c := by
  obtain ⟨u, hu, v, hv, w, hw, he⟩ :=
    modelParabolic_triple_product f.flag f.first (source.projection m)
  obtain ⟨a, ha⟩ := source.projection_surjective u
  obtain ⟨b, hb⟩ := source.projection_surjective v
  let c := (a * b)⁻¹ * m
  have hc : source.projection c = w := by
    dsimp [c]
    rw [map_mul, map_inv, map_mul, ha, hb, he]
    group
  refine ⟨a, ?_, b, ?_, c, ?_, ?_⟩
  · change source.projection a ∈ modelParabolic f.flag f.first
    rwa [ha]
  · change source.projection b ∈ modelParabolic f.flag (!f.first)
    rwa [hb]
  · change source.projection c ∈ modelParabolic f.flag f.first
    rwa [hc]
  · dsimp [c]
    group

/-- Fixation by the full first actor normalizes the literal midpoint-line
preimage, including the restored Z_alpha kernel. -/
theorem LocalConsequences.first_normalizes_linePreimage [Finite M]
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x) :
    f.ambient false ≤ normalizer (d.preimage (d.subspace (Z R c))) := by
  apply d.preimage_normalized _ (f.parabolic false)
  · exact (f.ambient_le false).trans (DistanceEight.V_normalized R (alpha R))
  · intro m hm v hv
    have hm' : m ∈ f.actor false := by rwa [f.actor_eq]
    have he := hlocal.first_fixed hv ⟨source.projection m, mem_map_of_mem _ hm'⟩
    change d.representation (source.projection m) v = v at he
    rwa [he]

/-- The seed contains the entire midpoint-line preimage. -/
theorem LocalConsequences.linePreimage_le
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) :
    d.preimage (d.subspace (Z R c)) ≤ d.preimage x.space := by
  have hz : Z R c ≤ V R (alpha R) := (Z_le_orbitSpan c).trans
    (orbitSpan_le_radius c ((cosetGraph R).dist_comm.trans hc).le)
  rw [LayerModule.preimage_subspace_eq d _ hz]
  exact sup_le (inf_le_left.trans x.Z_le_preimage) (hlocal.Z_le_preimage hc)

/-- The first parabolic preserves the midpoint centralizer inside V_alpha.
Normality is relative to that parabolic, not to the whole local group. -/
theorem LocalConsequences.first_normalizes_midpoint_intersection [Finite M]
    (common : CommonFacts R source geometry)
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) :
    f.ambient false ≤ normalizer (V R (alpha R) ⊓ Q R c : Subgroup (FreeAmalgam R)) := by
  have hz : Z R c ≤ V R (alpha R) := (Z_le_orbitSpan c).trans
    (orbitSpan_le_radius c ((cosetGraph R).dist_comm.trans hc).le)
  have ht : d.preimage (d.subspace (Z R c)) = Z R (alpha R) ⊔ Z R c := by
    rw [LayerModule.preimage_subspace_eq d _ hz,
      inf_eq_left.mpr (show Z R (alpha R) ≤ V R (alpha R) from Z_le_VBall R (alpha R) 2)]
  have hnormal := hlocal.first_normalizes_linePreimage
  rw [ht] at hnormal
  have hcenter : V R (alpha R) ≤ centralizer (Z R (alpha R) : Set (FreeAmalgam R)) :=
    (Flags.V_le_Q geometry common.large_distance _ rfl).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes (alpha R) rfl)))
  have he : V R (alpha R) ⊓ Q R c =
      V R (alpha R) ⊓ centralizer ((Z R (alpha R) ⊔ Z R c : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    rw [radius_inf_kernel common rfl hc]
    apply le_antisymm
    · refine le_inf inf_le_left (le_centralizer_iff.mpr (sup_le ?_ ?_))
      · exact le_centralizer_iff.mp (inf_le_left.trans hcenter)
      · exact le_centralizer_iff.mp inf_le_right
    · exact inf_le_inf_left _ (centralizer_le (show Z R c ≤ Z R (alpha R) ⊔ Z R c from le_sup_right))
  rw [he]
  exact (le_inf ((f.ambient_le false).trans (DistanceEight.V_normalized R (alpha R)))
    (hnormal.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf


/-- The full orbit span is generated by first-parabolic conjugates of the
seed. This uses the actual three-parabolic product, not a two-core formula. -/
theorem LocalConsequences.orbitSpan_eq_first_span [Finite M]
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) :
    orbitSpan c = conjugateSpanBy (d.preimage x.space) (f.ambient false) := by
  apply le_antisymm
  · apply iSup_le
    intro m
    apply map_le_iff_le_comap.mpr
    intro z hz
    obtain ⟨a, ha, b, hb, e, he, hm⟩ := f.triple_product m
    have hzV : Z R c ≤ V R (alpha R) := (Z_le_orbitSpan c).trans
      (orbitSpan_le_radius c ((cosetGraph R).dist_comm.trans hc).le)
    have hzT := LayerModule.le_preimage_subspace d (Z R c) hzV hz
    have heT := le_normalizer_iff.mp hlocal.first_normalizes_linePreimage
      (embedM R e) (mem_map_of_mem _ he) z hzT
    have hbX := le_normalizer_iff.mp x.preimage_normalized
      (embedM R b) (mem_map_of_mem _ hb) _ (hlocal.linePreimage_le hc heT)
    have hmem : embedM R a *
        (embedM R b * (embedM R e * z * (embedM R e)⁻¹) * (embedM R b)⁻¹) *
          (embedM R a)⁻¹ ∈ conjugateSpanBy (d.preimage x.space) (f.ambient false) :=
      subset_closure ⟨embedM R a, mem_map_of_mem _ ha, _, hbX, rfl⟩
    change embedM R m * z * (embedM R m)⁻¹ ∈
      conjugateSpanBy (d.preimage x.space) (f.ambient false)
    simpa only [hm, map_mul, mul_inv_rev, mul_assoc] using hmem
  · exact conjugateSpanBy_le (hlocal.preimage_le_orbitSpan hc)
      ((f.ambient_le false).trans (orbitSpan_normalized c))

/-- The source propagation conclusion follows from the local seed and
full flag geometry, with no further geometric or generation premise. -/
theorem orbitSpan_le_kernel_of_local [Finite M]
    (common : CommonFacts R source geometry)
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) :
    orbitSpan c ≤ Q R c := by
  rw [hlocal.orbitSpan_eq_first_span hc]
  exact (conjugateSpanBy_le (le_inf (d.preimage_le _) x.preimage_le)
    (hlocal.first_normalizes_midpoint_intersection common hc)).trans inf_le_right

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
