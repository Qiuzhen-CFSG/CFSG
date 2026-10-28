module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Faithfulness

/-!
# The source natural-section calculation at the selected generator

The noncentral seed supplies an element outside Q_d whose displacement on
V_d/Z_d has order at most two. The earlier edge bounds make Q_d act trivially.
The characteristic amalgam obstruction supplies nontrivial residual action.
The checked binary transvection recognition theorem therefore constructs a
split natural section with its actual quotient map, conjugation action and
marking. This is the full meaning of c(V_d/Z_d)=1.

The split section also proves that Vcirc_d intersects B_d inside Z_d: the
radical is exactly Z_d, and B_d is fixed modulo Z_d by the whole stabilizer.
The final theorem applies both results to the selected source generator.
No fixed-space equality for the incident edge actor is asserted here.

The imported small-displacement theorem is a general local representation
result; its later flag configuration is not assumed.
Source: Meierfrankenfeld--Stellmacher (1993), c(U)=1 on printed p.881 and
(4.6.7), printed p.904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
open Flags.RankOne.Propagation.Generation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The constituent assertion in (4.6.7), including literal natural coordinates
and splitting, follows from the selected seed without a recognition premise. -/
theorem natural_section_of_seed (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    Nonempty (Escape.NaturalSectionAt d (V R d) (Z R d)) := by
  have hd := seed_color a b d ha hab hdb
  let S := stabilizer R d
  let H := (V R d).subgroupOf S
  let N := (Z R d).subgroupOf S
  let := finite_stabilizer R d
  have hVS : V R d ≤ S := (radius_le_Q common d hd).trans (fun _ hx => hx.1)
  have hZS : Z R d ≤ S := Z_le_stabilizer R d
  obtain ⟨π, hπ, hker⟩ := Escape.Initial.Natural.exists_localProjection source d hd
  have hsmall : SmallDisplacementData π H N := by
    refine {
      projection_surjective := hπ
      kernel_le := fun _ hx => Z_le_VBall R d 2 hx
      normal_group := Escape.Initial.Natural.radius_normal d
      normal_kernel := geometry.Z_normal d
      elementary := Escape.Initial.Natural.elementary_radius_quotient
        source geometry common.large_distance (Initial.moduleFacts common) d hd
      kernel_action := ?_
      nontrivial_action := ?_
      small_actor := ?_ }
    · apply map_le_iff_le_comap.mp
      rw [hker, map_commutator, map_subgroupOf_eq_of_le hVS,
        map_subgroupOf_eq_of_le (show Q R d ≤ S from fun _ hx => hx.1)]
      exact edge.commutator_le_Z d hd
    · intro h
      apply Escape.Initial.Natural.Splitting.radius_moving_not_le_Z
        source geometry common.large_distance (Initial.moduleFacts common) d hd
      have hh := map_mono (f := S.subtype) h
      rw [map_commutator, map_subgroupOf_eq_of_le hVS,
        ← MonoidHom.range_eq_map, range_subtype, map_subgroupOf_eq_of_le hZS] at hh
      exact (commutator_mono le_rfl (Ltilde_le_stabilizer d)).trans hh
    · obtain ⟨x, hx, hxQ⟩ := SetLike.not_le_iff_exists.mp
        (seed_not_le_kernel geometry a b d ha hab hdb hseed)
      have hcolb : color R b = true := by
        have hn := adjacent_color_ne R hab
        cases hc : color R b <;> simp_all
      have hBaS : B R a (geometry.Z_normal a) ≤ S :=
        (B_le_radius common a ha).trans ((radius_le_Q common a ha).trans
          ((Q_le_adjacent_h R hcolb hab).trans (edge_actor_le_stabilizer b d hdb)))
      let y : S := ⟨x, hBaS hx⟩
      refine ⟨y, ?_, ?_⟩
      · intro hy
        have hh : y ∈ π.ker := hy
        rw [hker] at hh
        exact hxQ hh
      · have hm : (⁅H, zpowers y⁆).map S.subtype ≤
            ⁅B R a (geometry.Z_normal a), V R d⁆ := by
          rw [map_commutator, map_subgroupOf_eq_of_le hVS, MonoidHom.map_zpowers,
            commutator_comm]
          exact commutator_mono (zpowers_le.mpr hx) le_rfl
        have hbound := seed_displacement_index_le_two common hb edge a b d ha hab hdb
        have hfin : Finite (⁅B R a (geometry.Z_normal a), V R d⁆ : Subgroup (FreeAmalgam R)) := by
          let := finite_radius common a ha
          have hle := (seed_commutator_le_Z common hb edge a b d ha hab hdb).trans
            (show Z R a ≤ V R a from Z_le_VBall R a 2)
          exact Finite.of_injective (inclusion hle) (inclusion_injective _)
        rw [← relIndex_map_map_of_injective N ⁅H, zpowers y⁆ S.subtype_injective,
          map_subgroupOf_eq_of_le hZS]
        exact (relIndex_le_of_le_right hm index_ne_zero_of_finite).trans hbound
  obtain ⟨sectionData⟩ := singleNaturalSection_of_smallDisplacement hsmall
  refine ⟨{
    local_group := hVS
    kernel_le := Z_le_VBall R d 2
    projection := π
    module_section := ?_ }⟩
  simpa only [hker] using sectionData

/-- In the recognized section the moving and fixed subgroups meet only in Z.
The source edge bound makes the radical denominator exactly the literal Z. -/
theorem moving_fixed_intersection_le_Z (common : CommonFacts R source geometry)
    (edge : EdgeFacts R) (d : Vertex R) (hd : color R d = false)
    (s : Escape.NaturalSectionAt d (V R d) (Z R d)) :
    Vcirc R d ⊓ B R d (geometry.Z_normal d) ≤ Z R d := by
  let S := stabilizer R d
  let H := (V R d).subgroupOf S
  let N := (Z R d).subgroupOf S
  let Q₀ := (Q R d).subgroupOf S
  have hVS : V R d ≤ S := (radius_le_Q common d hd).trans (fun _ hx => hx.1)
  have hrad : Escape.radicalPreimage Q₀ H N = N := by
    apply sup_eq_left.mpr
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hVS,
      map_subgroupOf_eq_of_le (show Q R d ≤ S from fun _ hx => hx.1)]
    exact edge.commutator_le_Z d hd
  have hmove : Vcirc R d ≤ (Escape.movingPreimage Q₀ H N).map S.subtype := by
    have hm := map_mono (f := S.subtype)
      (show ⁅H, (⊤ : Subgroup S)⁆ ≤ Escape.movingPreimage Q₀ H N from le_sup_right)
    rw [map_commutator, map_subgroupOf_eq_of_le hVS,
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact (commutator_mono le_rfl (Ltilde_le_stabilizer d)).trans hm
  let := geometry.Z_normal d
  intro x hx
  let y : S := ⟨x, hVS (B_le_radius common d hd hx.2)⟩
  have hyM : y ∈ Escape.movingPreimage Q₀ H N := by
    obtain ⟨z, hz, hzx⟩ := hmove hx.1
    have hzy : z = y := Subtype.ext hzx
    exact hzy ▸ hz
  have hyC : y ∈ centralizerModulo H ⊤ N := by
    apply mem_centralizerModulo_iff.mpr
    refine ⟨B_le_radius common d hd hx.2, ?_⟩
    intro g _
    have hcomm := B_commutator_stabilizer_le_Z common edge d hd
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator g.property hx.2)
  have hI : Escape.movingPreimage Q₀ H N ⊓ centralizerModulo H ⊤ N = N := by
    have hi := s.module_section.intersection
    change Escape.movingPreimage Q₀ H N ⊓
      centralizerModulo H ⊤ (Escape.radicalPreimage Q₀ H N) =
        Escape.radicalPreimage Q₀ H N at hi
    simpa only [hrad] using hi
  exact (hI.le ⟨hyM, hyC⟩ : y ∈ N)

/-- The fixed/moving intersection bound at the selected generator, with its
natural-section premise discharged by the preceding source calculation. -/
theorem seed_moving_fixed_intersection_le_Z (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (edge : EdgeFacts R)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hseed : ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥) :
    Vcirc R d ⊓ B R d (geometry.Z_normal d) ≤ Z R d := by
  obtain ⟨s⟩ := natural_section_of_seed common hb edge a b d ha hab hdb hseed
  exact moving_fixed_intersection_le_Z common edge d (seed_color a b d ha hab hdb) s

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
