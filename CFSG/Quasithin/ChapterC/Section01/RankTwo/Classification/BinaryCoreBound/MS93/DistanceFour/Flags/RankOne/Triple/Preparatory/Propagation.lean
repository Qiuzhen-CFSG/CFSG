module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation

/-!
# Assembly of the midpoint commutator propagation argument

The midpoint conjugate span V₀ contains Z_alpha and inherits the assumed
commutator bound by U_alpha. In the single-section branch, centralizing
V_alpha-circ implies centralizing all of V_alpha by the common normalizer
transfer and the absence of fixed vectors in U_alpha. This contradicts
the selected midpoint's noncentrality. In the other branch, the actual
transported vertex normalizes V₀ by its distance bound. The displayed
commutator generation therefore puts Z_mu in V₀, proving propagation.

`flagPropagation_of_pairing_and_generation` isolates the assembly of the
two source branches. `flagPropagation` discharges both premises using the
actual SourceData application to (1.7)(i) from `Pairing` and the transported
generator construction from `Generation`. The natural flag section, the
selected kernel and the critical configuration remain explicit inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

namespace Propagation

/-- The pairing conclusion contradicts the critical midpoint's noncentrality.
Normalizer transfer replaces any need for a later radius-generation theorem. -/
theorem single_case_contradiction (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (hpair : ⁅midpointSpan p, Vcirc R (alpha R)⁆ = ⊥) : False := by
  have hSQ := (span_le_radius p).trans (V_le_Q geometry common.large_distance _ rfl)
  have hfixed : ⁅V R (alpha R), midpointSpan p⁆ ≤ fixedCore R (alpha R) :=
    common.normalization_transfer _ rfl _ hSQ (span_normal p)
      (by rw [commutator_comm, hpair]; exact bot_le)
  have hU : ⁅V R (alpha R), midpointSpan p⁆ ≤ U R (alpha R) := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (V_le_Q geometry common.large_distance _ rfl)).trans
      (span_commutator_le_U common p hseed)
  have hzero : ⁅V R (alpha R), midpointSpan p⁆ = ⊥ :=
    bot_unique ((le_inf hU (hfixed.trans inf_le_right)).trans
      (U_fixed_eq_bot common _ rfl).le)
  have hcent : midpointSpan p ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
    rw [commutator_comm] at hzero
    exact commutator_eq_bot_iff_le_centralizer.mp hzero
  apply span_not_le_B early p
  rw [early.B_eq_center _ rfl]
  intro x hx
  refine ⟨⟨x, span_le_radius p hx⟩, ?_, rfl⟩
  exact mem_center_iff.mpr (fun y => Subtype.ext (hcent hx y y.property))

namespace TransportedGenerator

/-- Transport preserves the source's distance-two ordered pair. -/
theorem distance {p : FlagCriticalData source geometry i} {t : Vertex R}
    (d : TransportedGenerator p t) : (cosetGraph R).dist d.lam t = 2 := by
  have h := dist_act R d.conjugator p.middle (alpha R)
  rw [d.middle_image, d.base_image] at h
  exact h.trans ((SimpleGraph.dist_comm ..).trans p.first_distance)

/-- The transported Z-layer normalizes the span at alpha by the critical radius. -/
theorem normalizes {p : FlagCriticalData source geometry i} {t : Vertex R}
    (d : TransportedGenerator p t) (hb : geometry.b R = 4)
    (ht : nu R geometry (alpha R) t) :
    Z R d.lam ≤ normalizer (midpointSpan p) := by
  have hc : color R d.lam = false := by
    rw [← d.middle_image, action_preserves_color]
    exact p.middle_color
  apply le_trans _ (span_normalized p)
  apply Z_le_stabilizer_of_dist_le d.lam (geometry.exists_critical d.lam hc)
  rw [geometry.distance_constant d.lam hc]
  change (cosetGraph R).dist d.lam (alpha R) ≤ geometry.b R
  have hh := (cosetGraph_connected R).dist_triangle
    (u := d.lam) (v := t) (w := alpha R)
  rw [d.distance, ht.1] at hh
  rw [hb]
  omega

/-- The displayed identity and actual local normality put Z_mu in V₀. -/
theorem Z_le_span [Finite M] {p : FlagCriticalData source geometry i} {t : Vertex R}
    (d : TransportedGenerator p t) (hb : geometry.b R = 4)
    (ht : nu R geometry (alpha R) t) : Z R t ≤ midpointSpan p := by
  rw [d.generation]
  apply sup_le
  · exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (d.normalizes hb ht))
  · exact inf_le_right.trans (Propagation.Z_le_span p)

end TransportedGenerator
end Propagation

open Propagation

/-- Conditional assembly of claim (2). The two remaining source arguments
are explicit premises and must both be proved before asserting flagPropagation. -/
theorem flagPropagation_of_pairing_and_generation [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i)
    (pairing : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R) →
      SingleSection p → ⁅midpointSpan p, Vcirc R (alpha R)⁆ = ⊥)
    (generation : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R) →
      ¬ SingleSection p → ∀ t, nu R geometry (alpha R) t →
      ¬ ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R) → Nonempty (TransportedGenerator p t)) :
    FlagPropagation p := by
  intro hseed t ht
  by_contra hbad
  have hsingle : ¬ SingleSection p := fun h =>
    single_case_contradiction common early p hseed (pairing hseed h)
  obtain ⟨d⟩ := generation hseed hsingle t ht hbad
  exact hbad ((commutator_mono (d.Z_le_span hb ht) le_rfl).trans
    (span_commutator_le_U common p hseed))

/-- Original MS93 (4.6.8), claim (2), p.906: the midpoint commutator bound
propagates to every vertex in nu(alpha). Both the single-section pairing
and the transported-generator branch are proved from the supplied inputs. -/
theorem flagPropagation [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i) :
    FlagPropagation p :=
  flagPropagation_of_pairing_and_generation common hb early p
    (singleSection_pairing common hb early i hkernel natural p)
    (transportedGenerator common hb early hkernel natural p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
