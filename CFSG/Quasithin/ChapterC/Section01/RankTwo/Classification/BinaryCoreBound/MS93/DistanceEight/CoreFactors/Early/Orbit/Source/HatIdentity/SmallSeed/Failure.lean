module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed

/-!
# The contrary third-containment consequence for the actual smaller seed

This applies the endpoint displacement and two-plane argument to the
hat-fixed seed constructed from the original source data. Its product,
commutator and both preceding kernel bounds are all discharged internally.
Failure of the third product containment therefore forces the distant
natural group into the local span and bounds its central commutator.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), first display p.898.
The final natural-quotient contradiction is still a separate source step.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed
open PathCentrality NormalizerTransfer Preliminary Preliminary.Decomposition Third
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem endpoint_failure [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (D : Subgroup (FreeAmalgam R)) (hHD : H R (p.walk.getVert (i-2)) ≤ D)
    (hD : D ≤ Q R (p.walk.getVert (i + 6)))
    (hnot : ¬ (D : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R))) :
    ⁅D, Z R (p.walk.getVert (i + 8))⁆ =
      H R (p.walk.getVert (i + 6)) := by
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hie : Even (i + 6) := hi.add (by decide)
  have hif : Even (i + 8) := hi.add (by decide)
  apply endpoint_commutator_eq_H common earlier
    (t := p.walk.getVert (i - 1)) (u := p.walk.getVert (i + 7))
    (p.even_color hi (by omega)) (p.even_color hib (by omega))
    (p.even_color hie (by omega)) (p.even_color hif (by omega))
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        p.adjacent (i := i - 1) (by omega))
  · simpa only [show i - 2 + 1 = i - 1 by omega] using
      p.adjacent (i := i - 2) (by omega)
  · simpa only [Nat.add_assoc] using p.adjacent (i := i + 6) (by omega)
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 7) (by omega))
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).2
  · simpa only [Nat.add_assoc] using
      (p.moving_neighbors source common earlier hie (by omega) (by omega)).2
  · exact forward_generation common earlier p (firstFactsOnPath source common earlier p)
      hi (by omega) hi6
  · exact hHD
  · exact hD
  · exact hnot

private theorem natural_failure [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (D : Subgroup (FreeAmalgam R)) (hHD : H R (p.walk.getVert (i-2)) ≤ D)
    (hQa : D ≤ Q R (p.walk.getVert i))
    (hD : D ≤ Q R (p.walk.getVert (i + 6)))
    (hsmall : ⁅D, Q R (p.walk.getVert i)⁆ ≤ H R (p.walk.getVert (i - 2)))
    (hnot : ¬ (D : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R))) :
    U R (p.walk.getVert (i + 4)) ≤ conjugatesIn
        (D) (stabilizer R (p.walk.getVert i)) ∧
      ⁅U R (p.walk.getVert (i + 4)), Q R (p.walk.getVert i)⁆ ≤
        U R (p.walk.getVert i) := by
  let J := conjugatesIn D (stabilizer R (p.walk.getVert i))
  have hib : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hic : Even (i + 2) := hi.add (by decide)
  have hid : Even (i + 4) := hi.add (by decide)
  have hie : Even (i + 6) := hi.add (by decide)
  have hba : p.walk.getVert i ∈ Escape.movingNeighbors geometry (p.walk.getVert (i - 2)) := by
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hib (by omega) (by omega)).2
  have hUa : U R (p.walk.getVert i) ≤ J := U_le_full_span common earlier
    (p.even_color hi (by omega)) (p.even_color hib (by omega)) hba D hHD
  have hHc : H R (p.walk.getVert (i + 2)) ≤ J :=
    (Orbit.H_le_neighbor_U common earlier (p.even_color hic (by omega)) (by
      simpa only [Nat.add_sub_cancel] using
        (p.moving_neighbors source common earlier hic (by omega) (by omega)).1)).trans hUa
  have hHe : H R (p.walk.getVert (i + 6)) ≤ J := by
    rw [← endpoint_failure common earlier p hi hi4 hi6 D hHD hD hnot]
    apply (commutator_mono (Escape.Initial.Natural.conjugatesIn_contains D _) ?_).trans
      (le_normalizer_iff_commutator_le_left.mp (conjugatesIn_normalized D (stabilizer R (p.walk.getVert i))))
    exact le_sup_right.trans (forward_generation common earlier p
      (firstFactsOnPath source common earlier p) hi (by omega) hi6).le
  have hUd : U R (p.walk.getVert (i + 4)) ≤ J := by
    rw [U_eq_neighbor_H_sup common earlier
      (c := p.walk.getVert (i + 2)) (e := p.walk.getVert (i + 6))
      (s := p.walk.getVert (i + 3)) (t := p.walk.getVert (i + 5))
      (p.even_color hic (by omega)) (p.even_color hid (by omega))
      (p.even_color hie (by omega))]
    · exact sup_le hHc hHe
    · simpa only [Nat.add_assoc] using p.adjacent (i := i + 2) (by omega)
    · exact adjacent_symm R (by
        simpa only [Nat.add_assoc] using p.adjacent (i := i + 3) (by omega))
    · exact adjacent_symm R (by
        simpa only [Nat.add_assoc] using p.adjacent (i := i + 5) (by omega))
    · simpa only [Nat.add_assoc] using p.adjacent (i := i + 4) (by omega)
    · simpa only [Nat.add_assoc] using
        (p.moving_neighbors source common earlier hic (by omega) (by omega)).2
    · simpa only [show i + 6 - 2 = i + 4 by omega] using
        (p.moving_neighbors source common earlier hie (by omega) (by omega)).1
    · simpa only [show i + 4 - 1 = i + 3 by omega, Nat.add_assoc] using
        p.edge_Z_ne (i + 4) hid (by omega) (by omega)
  refine ⟨hUd, (commutator_mono hUd le_rfl).trans ?_⟩
  exact full_span_commutator_le_U common earlier (p.even_color hib (by omega)) hba D
    hQa hsmall
/-- For the actual smaller seed, failure of the third containment forces
the natural-subgroup bound, with every preliminary input now discharged. -/
theorem failure_natural_bound_forward [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6)
    (hnot : ¬ (span R (p.walk.getVert i) (p.walk.getVert (i-2))
      (p.walk.getVert (i-1)) : Set (FreeAmalgam R)) ⊆
      (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
        (Q R (p.walk.getVert (i+8)) : Set (FreeAmalgam R))) :
    U R (p.walk.getVert (i+4)) ≤ conjugatesIn
        (span R (p.walk.getVert i) (p.walk.getVert (i-2)) (p.walk.getVert (i-1)))
        (stabilizer R (p.walk.getVert i)) ∧
      ⁅U R (p.walk.getVert (i+4)), Q R (p.walk.getVert i)⁆ ≤ U R (p.walk.getVert i) := by
  let w := forwardWindow common earlier p hi hi4 hi6
  have est := estimates_forward common earlier p hi hi4 hi6
  exact natural_failure common earlier p hi hi4 hi6 _
    ((H_le_seed common earlier w.color_b w.moving.1).trans (seed_le_span _ _ _))
    ((span_le_full w.moving.1).trans (span_le_Q earlier w.color_b w.moving.1))
    est.span_six est.span_comm hnot

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed
