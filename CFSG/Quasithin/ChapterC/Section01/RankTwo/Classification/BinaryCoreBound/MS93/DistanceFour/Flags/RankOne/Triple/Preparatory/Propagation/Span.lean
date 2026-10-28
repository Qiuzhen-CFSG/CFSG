module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.OrbitSpan

/-!
# The midpoint span in the flag propagation argument

The group V₀ on p.906 is the actual G_alpha-conjugate span of the chosen
Z-layer. It contains Z_alpha, is normal in the finite vertex stabilizer,
and lies in V_alpha. The hypothesis on the midpoint commutator propagates
to this span because U_alpha is invariant under the same stabilizer.
The critical configuration ensures that this span is not central in V_alpha.

These are the common group-theoretic steps of MS93 (4.6.8), claim (2).
They do not exclude the single-natural-section case or prove the displayed
generation of Z_mu in the other case.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), printed p.906.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The source V₀, with conjugation inside the original amalgam. -/
noncomputable def midpointSpan (p : FlagCriticalData source geometry i) :
    Subgroup (FreeAmalgam R) := Early.Containment.neighborSpan (alpha R) p.middle

/-- The original midpoint Z-layer is a generator of V₀. -/
theorem middle_le_span (p : FlagCriticalData source geometry i) :
    Z R p.middle ≤ midpointSpan p :=
  Early.Containment.Z_le_neighborSpan _ _

/-- V₀ is contained in the actual radius-two group. -/
theorem span_le_radius (p : FlagCriticalData source geometry i) :
    midpointSpan p ≤ V R (alpha R) :=
  Early.Containment.neighborSpan_le_radius _ _
    (by rw [SimpleGraph.dist_comm]; exact p.first_distance.le)

/-- The normalizer is the vertex stabilizer, not the infinite amalgam. -/
theorem span_normalized (p : FlagCriticalData source geometry i) :
    stabilizer R (alpha R) ≤ normalizer (midpointSpan p) :=
  Early.Containment.neighborSpan_normalized _ _

/-- Restriction to the vertex stabilizer gives genuine relative normality. -/
theorem span_normal (p : FlagCriticalData source geometry i) :
    ((midpointSpan p).subgroupOf (stabilizer R (alpha R))).Normal :=
  normal_subgroupOf_of_le_normalizer (span_normalized p)

/-- V₀ is finite because it is a subgroup of the finite vertex stabilizer. -/
theorem span_finite [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) : Finite (midpointSpan p) := by
  let := finite_stabilizer R (alpha R)
  exact Finite.of_injective
    (inclusion ((span_le_radius p).trans (geometry.V_local _ rfl common.large_distance)))
    (inclusion_injective _)

/-- The common edge omega-center and local transitivity put all of Z_alpha in V₀. -/
theorem Z_le_span [Finite M] (p : FlagCriticalData source geometry i) :
    Z R (alpha R) ≤ midpointSpan p := by
  have hZb : Z R (beta R) = edgeOmega R (beta R) := by
    rw [Z, if_neg (show color R (beta R) ≠ false from Bool.noConfusion)]
  have heb : edgeOmega R (beta R) ≤ midpointSpan p := by
    rw [← hZb]
    exact (edge_Z_le p.middle (beta R) p.middle_color
      (adjacent_symm R p.middle_neighbor)).trans (middle_le_span p)
  rw [Z, if_pos (show color R (alpha R) = false from rfl)]
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R (alpha R) (base_adjacent R) ht
  rw [← hgt, edgeOmega_act]
  have hn := span_normalized p ((stabilizer R (alpha R)).inv_mem hg)
  rw [mem_normalizer_iff_map_conj_eq] at hn
  exact (map_mono heb).trans_eq hn

/-- The hypothesis of claim (2) extends to every conjugate generating V₀. -/
theorem span_commutator_le_U (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) :
    ⁅midpointSpan p, Q R (alpha R)⁆ ≤ U R (alpha R) := by
  rw [midpointSpan, Early.Containment.neighborSpan_commutator common _ _ rfl
    (by rw [SimpleGraph.dist_comm]; exact p.first_distance.le)]
  exact iSup_conjugates_le_of_le_normalizer _ _ _ hseed (U_normalized _)

/-- The earlier commutator bound applies to V₀ without any RadiusFacts. -/
theorem span_commutator_le_Z (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) :
    ⁅midpointSpan p, Q R (alpha R)⁆ ≤ Z R (alpha R) :=
  (commutator_mono (span_le_radius p) le_rfl).trans (early.commutator_le_Z _ rfl)

/-- The selected noncentral triple rules out a central midpoint span. -/
theorem span_not_le_B (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) :
    ¬ midpointSpan p ≤ B R (alpha R) (geometry.Z_normal _) := by
  intro h
  exact (p.middle_mem_nu early).2 ((middle_le_span p).trans h)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
