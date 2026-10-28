module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.Configuration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.Basic

/-!
# Core bounds for the actual quotient action

The equality V = B VStar and the commutator bound [B,Ltilde] <= Z put the
moving radius subgroup, hence the core, in VStar. The starred intersection
and commutator conclusions then give core intersect B <= Z and [core,Q] <= U.
Finally V' = U bounds the core derived subgroup, and involution generation of
V puts every square in U. These deductions require no recognition theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9)--(4.6.10), printed p.908,
and the core/moving identity used in (4.6.11), printed p.909. All conclusions
remain conditional on the given CommonFacts and RadiusFacts.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common radius in
/-- The moving radius group lies in every starred span at the vertex. -/
theorem core_le_star (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    core R a ≤ VStar R geometry a b := by
  have hV := geometry.V_local a ha (by
    rw [geometry.distance_constant a ha]
    exact common.large_distance)
  have hL : Ltilde R a ≤ stabilizer R a := map_subtype_le _
  have hB : B R a (geometry.Z_normal a) ≤ V R a := by
    rw [radius.B_eq_center a ha]
    exact map_subtype_le _
  have hZ := Flags.Z_le_star geometry radius.toEarlyFacts common.large_distance a b ha hab
  have hnorm := Flags.star_normalized geometry a b
  have hp : V R a ≤ commutatorPreimage (stabilizer R a) (Ltilde R a)
      (VStar R geometry a b) := by
    rw [Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance a b ha hab]
    apply sup_le
    · exact le_commutatorPreimage (hB.trans hV)
        ((Flags.B_commutator_le_Z geometry a hV).trans hZ)
    · exact le_commutatorPreimage ((Flags.star_le_radius geometry a b).trans hV)
        (le_normalizer_iff_commutator_le_left.mp (hL.trans hnorm))
  rw [radius.core_eq_moving a ha, Vcirc]
  exact (commutator_mono hp le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hnorm)

include common radius in
/-- The starred intersection theorem bounds the core intersection with B. -/
theorem core_inter_B_le_Z (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    core R a ⊓ B R a (geometry.Z_normal a) ≤ Z R a := by
  rw [← radius.star_intersection a b ha hab]
  exact inf_le_inf_right _ (core_le_star source geometry common radius a b ha hab)

include common radius in
/-- The local kernel acts trivially on core/U. -/
theorem core_commutator_Q_le_U (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) : ⁅core R a, Q R a⁆ ≤ U R a := by
  rw [← radius.star_commutator a b ha hab]
  exact commutator_mono (core_le_star source geometry common radius a b ha hab) le_rfl

omit [Finite M] in
include radius in
/-- The actual core quotient by U is abelian. -/
theorem core_derived_le_U (a : Vertex R) (ha : color R a = false) :
    ⁅core R a, core R a⁆ ≤ U R a := by
  rw [← radius.radius_derived a ha]
  exact commutator_mono (radius.core_le_radius a ha) (radius.core_le_radius a ha)

omit [Finite M] in
include radius in
/-- Involution generation of the radius group makes every core square lie in U. -/
theorem core_square_mem_U (a : Vertex R) (ha : color R a = false)
    (x : core R a) : (x : FreeAmalgam R) ^ 2 ∈ U R a := by
  let P := V R a
  let f : P →* Abelianization P := (powMonoidHom 2).comp Abelianization.of
  have hle : P ≤ f.ker.map P.subtype := by
    change VBall R a 2 ≤ _
    conv_lhs => rw [← DistanceEight.VBall_omegaOne R a 2]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro y hy hy2
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    change (Abelianization.of (⟨y, hy⟩ : P)) ^ 2 = 1
    rw [← map_pow, show (⟨y, hy⟩ : P) ^ 2 = 1 from Subtype.ext hy2, map_one]
  obtain ⟨y, hy, he⟩ := hle (radius.core_le_radius a ha x.property)
  change (y : FreeAmalgam R) = x at he
  have hpow : y ^ 2 ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    change Abelianization.of (y ^ 2) = 1
    rw [map_pow]
    exact hy
  have hh := mem_map_of_mem P.subtype hpow
  rw [← radius.radius_derived a ha]
  simpa only [_root_.commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype,
    subtype_apply, coe_pow, he] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
