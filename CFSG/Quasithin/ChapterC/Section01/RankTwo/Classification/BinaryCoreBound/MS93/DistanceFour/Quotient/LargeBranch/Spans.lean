module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.Configuration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.Basic

/-!
# Actual orbit spans and noncentral edge generators

The embedM-conjugate span equals the full stabilizer-conjugate span. It is
normalized by that stabilizer and stays in the radius group. A noncentral
vertex puts it in every starred span. For a normalized subgroup which does
not centralize the radius group, the radius/center/star decomposition then
selects a noncommuting Z-layer on any specified edge star.

These are the geometric selection and containment steps used in the last
paragraph of MS93 (1993), (4.6.12), printed p.912. The rank-one recognition
of the selected spans remains separate.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
namespace LargeBranch
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The embedded M-orbit is exactly the orbit under the actual stabilizer. -/
theorem orbitSpan_eq_stabilizer_span (c : Vertex R) :
    orbitSpan c = ⨆ g : stabilizer R (alpha R),
      (Z R c).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom := by
  have hstab : stabilizer R (alpha R) = Mbar R := stabilizer_m_base R
  apply le_antisymm
  · apply iSup_le
    intro m
    exact le_iSup_of_le ⟨embedM R m, hstab.symm ▸ (show embedM R m ∈ Mbar R from ⟨m, rfl⟩)⟩ le_rfl
  · apply iSup_le
    intro g
    have hg : (g : FreeAmalgam R) ∈ Mbar R := hstab ▸ g.property
    obtain ⟨m, hm⟩ := hg
    exact le_iSup_of_le m (by simpa only [hm] using (le_rfl :
      (Z R c).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom ≤ _))

theorem Z_le_orbitSpan (c : Vertex R) : Z R c ≤ orbitSpan c := by
  intro x hx
  apply (le_iSup (fun m : M => (Z R c).map (MulAut.conj (embedM R m)).toMonoidHom) 1)
  exact ⟨x, hx, by simp⟩

theorem orbitSpan_normalized (c : Vertex R) :
    stabilizer R (alpha R) ≤ normalizer (orbitSpan c : Set (FreeAmalgam R)) := by
  rw [orbitSpan_eq_stabilizer_span]
  exact le_normalizer_iSup_conjugates _ _

theorem orbitSpan_le_of_normalized (c : Vertex R) (H : Subgroup (FreeAmalgam R))
    (hZH : Z R c ≤ H) (hn : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R))) :
    orbitSpan c ≤ H := by
  rw [orbitSpan_eq_stabilizer_span]
  exact iSup_conjugates_le_of_le_normalizer _ _ _ hZH hn

theorem orbitSpan_le_radius (c : Vertex R) (hc : (cosetGraph R).dist c (alpha R) ≤ 2) :
    orbitSpan c ≤ V R (alpha R) :=
  orbitSpan_le_of_normalized c _ (le_iSup_of_le c (le_iSup_of_le hc le_rfl))
    (DistanceEight.V_normalized R (alpha R))

theorem coreOrbit_normalized (c : Vertex R) (m : M) (x : core R (alpha R))
    (hx : x ∈ coreOrbit c) : coreAction (R := R) m x ∈ coreOrbit c := by
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  exact (mem_normalizer_iff.mp (orbitSpan_normalized c hm) _).mp hx

theorem orbitSpan_le_star [Finite M] (geometry : Geometry R)
    (early : EarlyFacts R geometry) (b c : Vertex R)
    (hb : Adjacent R (alpha R) b) (hc : nu R geometry (alpha R) c) :
    orbitSpan c ≤ VStar R geometry (alpha R) b :=
  orbitSpan_le_of_normalized c _ (Flags.nu_Z_le_star geometry early _ _ _ rfl hb hc)
    (Flags.star_normalized geometry _ _)

variable {L : Subgroup M} (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common

/-- The given critical segment escapes its midpoint kernel. -/
theorem midpoint_escape (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    ¬ V R (alpha R) ≤ Q R s.middle := by
  apply common.escape (alpha R) rfl s.endpoint s.critical s.middle s.second_distance
  rw [s.first_distance, s.critical.1]
  exact hb.symm

/-- Any normalized subgroup of the radius group which is not central has a
noncentral generator on each chosen edge star. This is the selection step
used for rho on printed p.912. -/
theorem exists_noncentral_neighbor [Finite M] (radius : RadiusFacts R geometry)
    (b : Vertex R) (hb : Adjacent R (alpha R) b)
    (A : Subgroup (FreeAmalgam R)) (hAV : A ≤ V R (alpha R))
    (hn : stabilizer R (alpha R) ≤ normalizer (A : Set (FreeAmalgam R)))
    (hne : ⁅V R (alpha R), A⁆ ≠ ⊥) :
    ∃ c, nu R geometry (alpha R) c ∧ Adjacent R b c ∧ ⁅Z R c, A⁆ ≠ ⊥ := by
  by_contra! hall
  have hEdge : edgeStar R geometry (alpha R) b ≤ centralizer (A : Set (FreeAmalgam R)) := by
    apply iSup_le
    intro c
    apply iSup_le
    intro hc
    exact commutator_eq_bot_iff_le_centralizer.mp (hall c hc.1 hc.2)
  have hStar : VStar R geometry (alpha R) b ≤ centralizer (A : Set (FreeAmalgam R)) :=
    iSup_conjugates_le_centralizer _ _ _ hn (commutator_eq_bot_iff_le_centralizer.mpr hEdge)
  have hB : B R (alpha R) (geometry.Z_normal (alpha R)) ≤ centralizer (A : Set (FreeAmalgam R)) := by
    rw [radius.B_eq_center (alpha R) rfl]
    rintro x ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hAV hy⟩)
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance _ _ rfl hb]
  exact sup_le hB hStar

end LargeBranch
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
