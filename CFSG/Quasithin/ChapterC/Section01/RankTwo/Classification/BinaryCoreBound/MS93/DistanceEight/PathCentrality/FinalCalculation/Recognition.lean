module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.ImageBounds.Involutions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple

/-!
# Recognizing the actual radius quotient in MS93 (4.4.5)

An involution outside the local kernel with displacement of order at most two
on V/Z forces the residual triple commutator into Z. This uses the nontrivial
two-core-fixed dual action and the binary small-displacement theorem. The
existing faithful-head recognition then constructs the full natural section.

For the source application, the index-two subgroup V_v intersect Q_c is fixed
modulo Z_v by a critical endpoint involution. The restriction bound gives the
required displacement on the whole V_v/Z_v. The two local calculations on
printed pp.894--895 remain explicit here; no contrary configuration is used.
-/

public section

open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
open Escape.Initial.Natural Escape.Initial.Natural.Triple
open LocalCommutator.CriticalCase.EscapeSelection.ImageBounds
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The small displacement is on the full quotient V/Z, so it also supplies
its residual triple bound, without assuming a natural section. -/
theorem radius_triple_of_small_involution
    (common : CommonFacts R source geometry) {v : Vertex R} (hv : color R v = false)
    (x : stabilizer R v) (hx : (x : FreeAmalgam R) ∉ Q R v)
    (hsmall : (Z R v).relIndex ⁅V R v, zpowers (x : FreeAmalgam R)⁆ ≤ 2) :
    ⁅⁅V R v, Q R v⁆, Ltilde R v⁆ ≤ Z R v := by
  let modules := LocalCommutator.moduleFacts common
  apply radius_triple_of_dual_fixed source geometry common.large_distance modules v hv
  let S := stabilizer R v
  let H := (V R v).subgroupOf S
  let N := (Z R v).subgroupOf S
  let := radius_normal (R := R) v
  let := geometry.Z_normal v
  let : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
    elementary_radius_quotient source geometry common.large_distance modules v hv
  let := finite_stabilizer R v
  obtain ⟨π, hπ, hker⟩ := exists_localProjection source v hv
  have hp : IsPGroup 2 π.ker := by
    rw [hker]
    exact (Q_isPGroup R source.two_group source.core_le v hv).comap_subtype
  have hne : (zpowers x).map π ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he (mem_zpowers x)
    rw [hker] at hk
    exact hx hk
  have hn : ¬ fixedSpace (sectionRepresentation H N).dual π.ker ≤
      fixedSpace (sectionRepresentation H N).dual (pResidual 2 S) := by
    rw [hker]
    exact radius_dual_fixedSpace_moving source geometry common.large_distance modules v hv
  have hi := relIndex_map_map_of_injective N ⁅H, zpowers x⁆ S.subtype_injective
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R v), map_commutator,
    map_subgroupOf_eq_of_le ((geometry.V_le_Q common.large_distance v hv).trans
      (fun _ hy => hy.1)), MonoidHom.map_zpowers] at hi
  have hd := moving_le_fixed_of_fixedSpace_not_le π hπ hp (zpowers x) hne
    (sectionRepresentation H N).dual
    (dual_fixedCodim_le_one H N (zpowers x) (hi.symm ▸ hsmall)) hn
  rw [hker] at hd
  exact hd

/-- The actual small radius involution supplies every clause of c(V_v/Z_v)=1. -/
theorem natural_section_of_small_involution
    (common : CommonFacts R source geometry) {v : Vertex R} (hv : color R v = false)
    (hs : HasSmallRadiusInvolution v) :
    Nonempty (Escape.NaturalSectionAt v (V R v) (Z R v)) := by
  obtain ⟨x, hx, htwo, hsmall⟩ := hs
  exact radius_section_of_small_displacement common common.large_distance hv
    (radius_triple_of_small_involution common hv x hx hsmall) x hx htwo hsmall

/-- An index-two fixed hyperplane gives the full-quotient involution in (4.4.5).
The critical pair supplies its actual nontrivial image and local membership. -/
theorem small_involution_of_critical_hyperplane
    (common : CommonFacts R source geometry)
    {d v c : Vertex R} (p : CriticalPath R geometry d v)
    (hindex : (Q R c).relIndex (V R v) ≤ 2)
    (hcomm : ⁅Z R d, V R v ⊓ Q R c⁆ ≤ ⁅Z R d, Z R v⁆) :
    HasSmallRadiusInvolution v := by
  let S := stabilizer R v
  let H := Escape.Initial.Natural.Splitting.localRadius v
  let N := Escape.Initial.Natural.Splitting.localZ v
  let K := (V R v ⊓ Q R c).subgroupOf S
  have hHS : V R v ≤ S :=
    (geometry.V_le_Q common.large_distance v p.end_color).trans (fun _ hy => hy.1)
  have hZS : Z R d ≤ S := (p.reverse common).endpoint_Z_le_start_stabilizer (by have := common.large_distance; omega)
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp p.critical.2
  let x : S := ⟨z, hZS hz⟩
  have htwo : x ^ 2 = 1 := by
    let := geometry.Z_elementary (by have := common.large_distance; omega) d p.start_color
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz)
  have hcritical : ⁅Z R d, Z R v⁆ ≤ Z R v :=
    le_normalizer_iff_commutator_le_right.mp (hZS.trans (Z_normalized R v))
  have hKN : ⁅K, zpowers x⁆ ≤ N := by
    intro y hy
    have hm := mem_map_of_mem S.subtype hy
    rw [map_commutator, map_subgroupOf_eq_of_le (inf_le_left.trans hHS),
      MonoidHom.map_zpowers] at hm
    exact ((commutator_mono le_rfl (zpowers_le.mpr hz)).trans
      ((commutator_comm (V R v ⊓ Q R c) (Z R d)) ▸ hcomm)).trans hcritical hm
  let := finite_stabilizer R v
  let := geometry.Z_normal v
  have hderived : ⁅H, H⁆ ≤ N := by
    intro y hy
    have hm := mem_map_of_mem S.subtype hy
    rw [map_commutator, map_subgroupOf_eq_of_le hHS] at hm
    exact radius_derived_le_Z source geometry common.large_distance
      (LocalCommutator.moduleFacts common) v p.end_color hm
  have hidx : K.relIndex H = (Q R c).relIndex (V R v) := by
    rw [← relIndex_map_map_of_injective K H S.subtype_injective,
      map_subgroupOf_eq_of_le (inf_le_left.trans hHS), map_subgroupOf_eq_of_le hHS,
      inf_relIndex_left]
  have hdisp := quotient_commutator_relIndex_le_mul_of_restriction
    H K N N (comap_mono inf_le_left) (fun _ hy => Z_le_VBall R v 2 hy)
    (fun _ hy => Z_le_VBall R v 2 hy) inferInstance hderived
    x (by rw [normalizer_eq_top]; trivial) hKN
  rw [relIndex_self, mul_one, hidx, relIndex_sup_right] at hdisp
  have hi := relIndex_map_map_of_injective N ⁅H, zpowers x⁆ S.subtype_injective
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R v), map_commutator,
    map_subgroupOf_eq_of_le hHS, MonoidHom.map_zpowers] at hi
  exact ⟨x, hzQ, htwo, hi.trans_le (hdisp.trans hindex)⟩

/-- Source (4.4.5) recognition from its two preceding local calculations. -/
theorem natural_section_of_critical_hyperplane
    (common : CommonFacts R source geometry)
    {d v c : Vertex R} (p : CriticalPath R geometry d v)
    (hindex : (Q R c).relIndex (V R v) ≤ 2)
    (hcomm : ⁅Z R d, V R v ⊓ Q R c⁆ ≤ ⁅Z R d, Z R v⁆) :
    Nonempty (Escape.NaturalSectionAt v (V R v) (Z R v)) :=
  natural_section_of_small_involution common p.end_color
    (small_involution_of_critical_hyperplane common p hindex hcomm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
