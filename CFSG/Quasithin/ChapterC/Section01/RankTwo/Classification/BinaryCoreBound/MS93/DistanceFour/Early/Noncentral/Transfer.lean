module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint

/-!
# The second MS93 (4.6.6) moving-kernel transfer

The critical edge-plane comparison implies the moving-kernel bound at every
M-vertex under the contrary central-derived hypothesis. The reduction finds
a critical path through each generator outside B, preserving its common edge
and its actual vertex kernels. Midpoint centrality of the edge plane then
bounds the generator's displacement by the local kernel.

The source midpoint comparison on pp.903--904 now discharges the hmid
premise of the preserved conditional reduction. The resulting
moving_kernel_fixed_of_derived_central has exactly the input required by
Early/Assembly.lean, without a further central-span or escape premise.

Source: Meierfrankenfeld--Stellmacher (1993), second (4.6.6), pp.903--904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Apply critical midpoint edge centrality to all nonfixed radius generators.
The midpoint comparison is the one remaining source premise. -/
theorem moving_kernel_fixed_of_critical_edge_central [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry)
    (hmid : ∀ (d e c b : Vertex R) (hd : color R d = false),
      CriticalPair R d e (geometry.exists_critical d hd) →
      (cosetGraph R).dist d c = 2 → (cosetGraph R).dist c e = 2 →
      Adjacent R d b → Adjacent R c b →
      ⁅V R d, V R d⁆ ≤ (center (stabilizer R d)).map (stabilizer R d).subtype →
      ⁅Z R d, Q R b⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype)
    (a : Vertex R) (ha : color R a = false)
    (hcentral : ⁅V R a, V R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype) :
    ⁅Vcirc R a, Q R a⁆ ≤ fixedCore R a := by
  apply moving_kernel_fixed_of_nonfixed_generator_bounds common a ha
  intro d hnu
  have hd : color R d = false :=
    (color_eq_of_dist_even R d a (by rw [hnu.1]; decide)).trans ha
  obtain ⟨e, hcrit, hae⟩ := critical_through_nonfixed_generator common hb initial a d ha hd hnu
  obtain ⟨b, hdb, hab⟩ := exists_common_neighbor_of_dist_two R d a hnu.1
  have hbcol : color R b = true := by
    have hn := adjacent_color_ne R hab
    cases hh : color R b <;> simp_all
  have hbound := (commutator_mono le_rfl (Q_le_adjacent_h R hbcol hab)).trans
    (hmid d e a b hd hcrit hnu.1 hae hdb hab (derived_central_at_all a ha hcentral d hd))
  rintro x hx y hy
  obtain ⟨z, hz, rfl⟩ := hbound hx
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)

/-- The source midpoint comparison supplies the moving-kernel bound under
centrality of the radius-derived subgroup, with all local comparison steps
discharged. This is the transfer input of `earlyFacts_of_local_steps`. -/
theorem moving_kernel_fixed_of_derived_central [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry) (edge : EdgeFacts R)
    (a : Vertex R) (ha : color R a = false)
    (hcentral : ⁅V R a, V R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype) :
    ⁅Vcirc R a, Q R a⁆ ≤ fixedCore R a := by
  exact moving_kernel_fixed_of_critical_edge_central common hb initial
    (critical_edge_plane_central_of_derived_central common hb initial edge) a ha hcentral

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
