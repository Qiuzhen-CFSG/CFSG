module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Quotients
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Cardinalities.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Residual

/-!
# Geometric preparation for the two rank-one sections

The natural moving layer meets the intrinsic local center trivially. The
radius-derived equality therefore gives Bzero = B_alpha, and it makes
every critical midpoint displacement noncentral. A genuine marked frame
from the earlier (4.6.8) construction then normalizes K and Y and fixes
Z_c modulo Z_alpha. The source residual is kept distinct from the full
parabolic and its SL2(2) quotient.

The frame constructor is deliberately conditional on the earlier flag
output. No construction of that output, exact index, or natural-module
recognition is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9) and (4.6.12)(1)--(2),
printed pp.908 and 910; the marked flag is selected on printed p.905.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
open Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common in
/-- The natural moving layer has trivial intersection with the intrinsic local center. -/
theorem U_inf_localCenter_eq_bot :
    U R (alpha R) ⊓ (center (stabilizer R (alpha R))).map
      (stabilizer R (alpha R)).subtype = ⊥ := by
  apply le_bot_iff.mp
  rw [← Flags.U_fixed_eq_bot common (alpha R) rfl]
  apply inf_le_inf_left
  rintro x ⟨z, hz, rfl⟩ l hl
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨l, map_subtype_le _ hl⟩)

include common radius in
/-- The supplied derived equality identifies the earlier quotient centralizer Bzero. -/
theorem Bzero_eq_B :
    Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)) := by
  have hV := geometry.V_local (alpha R) rfl common.large_distance
  have hB := Bzero_le_radius geometry (alpha R)
  have hcomm : ⁅Bzero geometry (alpha R), V R (alpha R)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← U_inf_localCenter_eq_bot common]
    refine le_inf ?_ ?_
    · exact (commutator_mono hB le_rfl).trans_eq (radius.radius_derived (alpha R) rfl)
    · exact ((le_Bzero_iff geometry (alpha R) hV _).mp le_rfl).2.trans inf_le_right
  rw [radius.B_eq_center (alpha R) rfl]
  apply le_antisymm _ (radius_center_le_Bzero geometry (alpha R) hV)
  intro x hx
  refine ⟨⟨x, hB hx⟩, mem_center_iff.mpr ?_, rfl⟩
  intro v
  exact Subtype.ext (commutator_eq_bot_iff_le_centralizer.mp hcomm hx v v.property)

include common radius in
/-- Every critical midpoint has noncentral displacement; this uses no branch assumption. -/
theorem midpoint_displacement_noncentral [Finite M]
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    ¬ ⁅Z R s.middle, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  intro hc
  have hZV : Z R s.middle ≤ V R (alpha R) :=
    le_iSup_of_le s.middle (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm, s.first_distance]) le_rfl)
  have hzero : ⁅Z R s.middle, V R (alpha R)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← U_inf_localCenter_eq_bot common]
    exact le_inf ((commutator_mono hZV le_rfl).trans_eq
      (radius.radius_derived (alpha R) rfl)) hc
  have hcentral : V R (alpha R) ≤ centralizer (Z R s.middle : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have he := radius_inf_kernel common rfl s.first_distance
  rw [inf_eq_left.mpr hcentral] at he
  exact midpoint_escape source common hb s (inf_eq_left.mp he)

/-- A source flag witness retains its actual intrinsic edge core and triple bound.
Its construction from the source assumptions belongs to (4.6.8). -/
structure Frame (source : LocalSource L R) where
  orientation : Bool
  edge_kernel : flagKernel source orientation = Q R (beta R)
  triple : ⁅⁅V R (beta R), flagResidual source orientation⁆, V R (alpha R)⁆ ≤
    (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype

/-- Repackage the proved flag output without changing its parabolics or its residual. -/
theorem exists_frame_of_flagControl (control : FlagControl source) : Nonempty (Frame source) := by
  obtain ⟨i, hi, ht⟩ := control
  exact ⟨⟨i, hi, ht⟩⟩

variable [Finite M] (f : Frame source)

include common radius in
/-- The selected residual fixes Z_c modulo the original Z_alpha layer. -/
theorem residual_commutator_le_Z {c : Vertex R} (hbc : Adjacent R (beta R) c) :
    ⁅Z R c, flagResidual source f.orientation⁆ ≤ Z R (alpha R) := by
  have hZ : Z R c ≤ V R (beta R) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le c (le_iSup_of_le hbc le_rfl)
  exact (commutator_mono hZ le_rfl).trans
    (flag_commutator_le_Z_of_Bzero source geometry common.large_distance radius.toEarlyFacts
      f.orientation f.edge_kernel f.triple (Bzero_eq_B common radius))

include common radius in
/-- The same residual normalizes the literal intersection K. -/
theorem residual_normalizes_intersection {c : Vertex R}
    (hd : (cosetGraph R).dist (alpha R) c = 2) (hbc : Adjacent R (beta R) c) :
    flagResidual source f.orientation ≤ normalizer (intersection c) := by
  have hZ : Z R c ≤ V R (beta R) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le c (le_iSup_of_le hbc le_rfl)
  have hc : color R c = false := distance_two_color rfl hd
  have hnZ : flagResidual source f.orientation ≤ normalizer (Z R c) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hZ le_rfl).trans
      (flag_commutator_le_edge_Z_of_Bzero source geometry common.large_distance
        radius.toEarlyFacts f.orientation f.edge_kernel f.triple (Bzero_eq_B common radius))).trans
          (Flags.edge_Z_le c (beta R) hc (adjacent_symm R hbc))
  change _ ≤ normalizer ((V R (alpha R) ⊓ Q R c : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))
  rw [radius_inf_kernel common rfl hd]
  apply le_normalizer_inf
  · exact (flagResidual_le source f.orientation).trans
      ((flagParabolic_le source f.orientation).trans (DistanceEight.V_normalized R _))
  · exact hnZ.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))

include common radius in
/-- The residual also normalizes the literal fixed-point preimage Y. -/
theorem residual_normalizes_fixedPreimage {c : Vertex R}
    (hd : (cosetGraph R).dist (alpha R) c = 2) (hbc : Adjacent R (beta R) c) :
    flagResidual source f.orientation ≤ normalizer (fixedPreimage c) := by
  apply commutatorPreimage_normalized
  · exact inf_le_left.trans
      ((geometry.V_local (alpha R) rfl common.large_distance).trans (Z_normalized R _))
  · exact residual_normalizes_intersection common radius f hd hbc
  · rw [← f.edge_kernel]
    exact (flagResidual_le source f.orientation).trans (flagKernel_normalized source f.orientation)
  · exact (flagResidual_le source f.orientation).trans
      ((flagParabolic_le source f.orientation).trans (Z_normalized R _))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
