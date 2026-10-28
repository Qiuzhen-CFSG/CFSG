module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.SecondCommutator
public import Theory.GroupAction.CyclicQuotientRestrictionBound

/-!
# The literal displacement bound from the R₂ containment

Assume R₂ lies in Z_delta D_delta and [V_delta : V_delta intersect Q_a]=2.
Choose an actual involution of Z_(a+2) outside Q_delta by criticality.
Its commutator map on the elementary radius group vanishes modulo
Z_delta D_delta on the intersection with Q_a, so the full displacement
modulo that denominator has order at most two.

All quotients are formed inside G_delta. Intersecting the denominator
with V_delta supplies its relative normality; the subtype inclusion
recovers the displayed ambient relative index. The result retains the
chosen involution and its membership in the original critical Z-layer.

The denominator is Z_delta D_delta, not Z_delta. Recognizing a full
natural section from this bound requires an additional source argument;
no removal of the fixed-core factor or splitting is asserted here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, the R₂ noncontainment step.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}
  (s : Configuration p) (hb : 4 < geometry.b R)

include hb

/-- The index-two kernel bounds displacement on the actual fixed-core quotient. -/
theorem small_fixed_displacement_of_secondCommutator_le
    (common : CommonFacts R source geometry)
    (hindex : (Q R a).relIndex (V R s.delta) = 2)
    (hcontain : s.secondCommutator ≤ Z R s.delta ⊔ fixedCore R s.delta) :
    ∃ x : stabilizer R s.delta,
      (x : FreeAmalgam R) ∈ Z R (p.walk.getVert 2) ∧
      (x : FreeAmalgam R) ∉ Q R s.delta ∧ x ^ 2 = 1 ∧
      (Z R s.delta ⊔ fixedCore R s.delta).relIndex
        ⁅V R s.delta, zpowers (x : FreeAmalgam R)⁆ ≤ 2 := by
  let S := stabilizer R s.delta
  let H := (V R s.delta).subgroupOf S
  let D := (Z R s.delta ⊔ fixedCore R s.delta).subgroupOf S
  let N := H ⊓ D
  let K := (V R s.delta ⊓ Q R a).subgroupOf S
  have hHS : V R s.delta ≤ S :=
    (geometry.V_le_Q (by omega) s.delta s.delta_color).trans (fun _ hy => hy.1)
  have hDS : Z R s.delta ⊔ fixedCore R s.delta ≤ S :=
    sup_le (Z_le_stabilizer R s.delta) (fun _ hy => hy.1.1)
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide)
  have hrev := common.critical_reverse s.delta s.delta_color _ hc (s.backward_critical hb)
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hrev.2
  let x : S := ⟨z, s.second_Z_le_delta_stabilizer hb hz⟩
  have htwo : x ^ 2 = 1 := by
    let := geometry.Z_elementary (by omega) (p.walk.getVert 2) hc
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz)
  let := finite_stabilizer R s.delta
  let : H.Normal := Escape.Initial.Natural.radius_normal s.delta
  let : D.Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf (Z_normalized R s.delta) (fixedCore_normalized R s.delta)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hKN : ⁅K, zpowers x⁆ ≤ N := by
    apply le_inf
    · exact (commutator_mono (comap_mono inf_le_left) le_rfl).trans
        (commutator_le_left H _)
    · intro y hy
      have hm := mem_map_of_mem S.subtype hy
      rw [map_commutator, map_subgroupOf_eq_of_le (inf_le_left.trans hHS),
        MonoidHom.map_zpowers] at hm
      have hbound : ⁅V R s.delta ⊓ Q R a, zpowers z⁆ ≤ s.secondCommutator := by
        rw [commutator_comm]
        exact commutator_mono (zpowers_le.mpr hz) le_rfl
      exact hcontain (hbound hm)
  have hderived : ⁅H, H⁆ ≤ N := by
    let := s.radius_elementary hb
    let := IsElementaryAbelian.subgroupOf (p := 2) hHS
    have hcomm : ⁅H, H⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    rw [hcomm]
    exact bot_le
  have hidx : K.relIndex H = 2 := by
    rw [← relIndex_map_map_of_injective K H S.subtype_injective,
      map_subgroupOf_eq_of_le (inf_le_left.trans hHS), map_subgroupOf_eq_of_le hHS,
      inf_relIndex_left, hindex]
  have hdisp := quotient_commutator_relIndex_le_mul_of_restriction
    H K N N (comap_mono inf_le_left) inf_le_left inf_le_left
    inferInstance hderived x (by rw [normalizer_eq_top]; trivial) hKN
  rw [relIndex_self, mul_one, hidx, relIndex_sup_right] at hdisp
  have hDdisp : D.relIndex ⁅H, zpowers x⁆ ≤ 2 :=
    (relIndex_le_of_le_left (show N ≤ D from inf_le_right)
      (by exact index_ne_zero_of_finite)).trans hdisp
  have hi := relIndex_map_map_of_injective D ⁅H, zpowers x⁆ S.subtype_injective
  rw [map_subgroupOf_eq_of_le hDS, map_commutator,
    map_subgroupOf_eq_of_le hHS, MonoidHom.map_zpowers] at hi
  exact ⟨x, hz, hzQ, htwo, hi.trans_le hDdisp⟩

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
