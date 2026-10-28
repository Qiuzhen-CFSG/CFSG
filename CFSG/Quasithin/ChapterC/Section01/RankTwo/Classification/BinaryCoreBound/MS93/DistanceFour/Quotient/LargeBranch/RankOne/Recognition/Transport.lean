module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Modules


/-!
# Moving a critical segment onto the distinguished edge

Local transitivity sends the common neighbor of alpha and the midpoint to
beta. The resulting segment stays critical, its intersection stays in the
same source branch, and its full stabilizer orbit span is unchanged.
Containment in the midpoint kernel transports in both directions.

This supplies the geometric change of notation preceding the rank-one
argument of MS93 (1993), (4.6.12), printed pp.910--912. It does not construct
the rank-one sections or recognize the quotient of that unchanged span.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {common : CommonFacts R source geometry}

private theorem orbitSpan_act_le (c : Vertex R) (g : FreeAmalgam R)
    (hg : g ∈ stabilizer R (alpha R)) : orbitSpan (act R g c) ≤ orbitSpan c := by
  apply orbitSpan_le_of_normalized _ _ _ (orbitSpan_normalized c)
  rw [Z_act]
  have hn := mem_normalizer_iff_map_conj_eq.mp
    (orbitSpan_normalized c ((stabilizer R (alpha R)).inv_mem hg))
  exact (map_mono (Z_le_orbitSpan c)).trans_eq hn

/-- Changing the midpoint by a base stabilizer element leaves its full orbit span unchanged. -/
theorem orbitSpan_act_eq (c : Vertex R) (g : FreeAmalgam R)
    (hg : g ∈ stabilizer R (alpha R)) : orbitSpan (act R g c) = orbitSpan c := by
  apply le_antisymm (orbitSpan_act_le c g hg)
  have h := orbitSpan_act_le (act R g c) g⁻¹ ((stabilizer R (alpha R)).inv_mem hg)
  simpa only [← act_mul, mul_inv_cancel, act_one] using h


/-- Translate both ends of the critical segment while fixing its base vertex. -/
noncomputable def translateSegment (s : CriticalSegment geometry) (g : FreeAmalgam R)
    (hg : g ∈ stabilizer R (alpha R)) : CriticalSegment geometry where
  endpoint := act R g s.endpoint
  middle := act R g s.middle
  critical := by
    have hga : act R g (alpha R) = alpha R := hg
    have hh := (criticalPair_act_iff R g (alpha R) s.endpoint
      (geometry.exists_critical (alpha R) rfl)
      (geometry.exists_critical (act R g (alpha R)) (by rw [action_preserves_color]; rfl))).mpr s.critical
    simpa only [hga] using hh
  first_distance := by
    have hga : act R g (alpha R) = alpha R := hg
    have h := dist_act R g (alpha R) s.middle
    rw [hga] at h
    exact h.trans s.first_distance
  second_distance := (dist_act R g s.middle s.endpoint).trans s.second_distance


/-- Translation preserves the literal commutator containment distinguishing the two branches. -/
theorem translateSegment_small_iff (s : CriticalSegment geometry) (g : FreeAmalgam R)
    (hg : g ∈ stabilizer R (alpha R)) :
    (translateSegment s g hg).SmallIntersection ↔ s.SmallIntersection := by
  have hga : act R g (alpha R) = alpha R := hg
  have hV : V R (alpha R) = (V R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← V_act, hga]
  have hZ : Z R (alpha R) = (Z R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← Z_act, hga]
  change ⁅V R (alpha R) ⊓ Q R (act R g s.middle), V R (act R g s.middle)⁆ ≤
    Z R (alpha R) ↔ _
  conv_lhs => rw [hV, hZ, Q_act, V_act,
    ← map_inf _ _ _ (MulAut.conj g⁻¹).injective, ← map_commutator]
  exact map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective


/-- Kernel containment is equivalent for the original and translated midpoint. -/
theorem orbitSpan_le_kernel_act_iff (c : Vertex R) (g : FreeAmalgam R)
    (hg : g ∈ stabilizer R (alpha R)) :
    orbitSpan (act R g c) ≤ Q R (act R g c) ↔ orbitSpan c ≤ Q R c := by
  have hn := mem_normalizer_iff_map_conj_eq.mp
    (orbitSpan_normalized c ((stabilizer R (alpha R)).inv_mem hg))
  conv_lhs => rw [orbitSpan_act_eq c g hg, Q_act, ← hn]
  exact map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective


/-- Every critical segment has a base-stabilizer translate whose midpoint is adjacent to beta. -/
theorem exists_segment_on_base_edge [Finite M] (s : CriticalSegment geometry) :
    ∃ (g : FreeAmalgam R) (hg : g ∈ stabilizer R (alpha R)),
      Adjacent R (beta R) (translateSegment s g hg).middle := by
  obtain ⟨b, hab, hbc⟩ := distance_two_neighbor s.first_distance
  obtain ⟨g, hg, hgb⟩ := stabilizer_transitive_neighbors R (alpha R) hab (base_adjacent R)
  refine ⟨g, hg, ?_⟩
  have h := (adjacent_act_iff R g b s.middle).mpr hbc
  rwa [hgb] at h


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
