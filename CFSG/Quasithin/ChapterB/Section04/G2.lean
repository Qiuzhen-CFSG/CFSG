module

public import CFSG.Quasithin.ChapterB.Defs
public import CFSG.Quasithin.ChapterB.Section04.G2.Transport
public import CFSG.Quasithin.ChapterB.Section04.G2.Extensions
public import CFSG.Quasithin.ChapterB.Section04.G2.SourceGeometry
public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.FirstCohomologyG2Natural.Commutant
public import Theory.Representation.G2.NaturalInvolutionRank
public import Theory.Representation.G2BinaryParabolicFixed
public import Theory.Representation.G2BinarySylowFixedSpace
public import Theory.Representation.BinaryOffender.Basic
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# The `G₂` row of B.4.6

This file keeps the two levels occurring in the printed lemma separate.  The
theorems in `Atlas.G2.Natural` are calculations on the literal split-octonion
model and its *actual* derived subgroup; they therefore include the exceptional
binary case without identifying `G₂(2)` with `G₂(2)'`.  The source assembly is
parametrised by the marked extension data used in B.4.6.  In particular, the
subgroups called `L` and `E(L)` are separate fields and the fourteen source
clauses are carried by the corresponding geometric interfaces.

The cohomological and parabolic interfaces are intentionally stated on the
original action.  This avoids replacing the source quotient by an unrelated
record projection, and lets Chapter K and the B.4 assembly discharge the
remaining extension hypotheses with their own literal maps.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma B.4.6, printed pp. 88--90; concrete natural-module calculations are
from I.1.6 and I.2.3 and the attributed split-octonion model.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.Section04.G2

/-! ## Concrete natural-module calculations -/

namespace Natural

variable {K : Type*} [Field K] [CharP K 2]

/-- The six-dimensional natural module has the expected dimension over the
coefficient field, including `K = F₂`. -/
theorem finrank :
    Module.finrank K (Atlas.G2.Natural.Space K) = 6 :=
  Atlas.G2.Natural.finrank_space K

/-- The actual derived group is transitive on nonzero natural vectors.  The
binary branch is handled inside `derivedAction_transitive`; no full-model
surjectivity is used here. -/
theorem transitive [Finite K] {x y : Atlas.G2.Natural.Space K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : commutator (Atlas.G2.Model K),
      Atlas.G2.Natural.derivedAction K g x = y :=
  Atlas.G2.Natural.derivedAction_transitive K x y hx hy

/-- The additive commutant of the actual derived action consists of scalar
maps.  This is the `End_F₂(V̄)=F` part of B.4.6(1), with the field action kept
explicit. -/
theorem scalar_commutant (f : Atlas.G2.Natural.Space K →+ Atlas.G2.Natural.Space K)
    (hf : ∀ (g : commutator (Atlas.G2.Model K)) v,
      f (Atlas.G2.Natural.derivedAction K g v) =
        Atlas.G2.Natural.derivedAction K g (f v)) :
    ∃ c : K, ∀ v, f v = c • v :=
  Atlas.G2.Natural.exists_scalar_of_additive_commutes_derived f hf

/-- Every nonidentity involution in the literal natural action has displacement
rank two or three.  The upper and lower bounds are useful independently of the
extension assembly. -/
theorem involution_displacement [Finite K] (g : Atlas.G2.Model K)
    (hne : g ≠ 1) (hg : g * g = 1) :
    2 ≤ Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
        (Atlas.G2.Natural.action K g) ∧
      Representation.BinaryOffender.NaturalTensor.operatorFixedCodim
        (Atlas.G2.Natural.action K g) ≤ 3 :=
  Atlas.G2.Natural.InvolutionRank.operatorFixedCodim_bounds g hne hg

end Natural

/-! ## Marked B.4.6 input and source clauses -/

section Source

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The marked extension and local geometry used by the B.4.6 source proof.

`L` is the distinguished quasisimple section and `EL` is the literal subgroup
`E(L)` acting on the original module.  The first six fields retain the source
module data; the remaining fields are the local geometric statements proved by
the corresponding root/parabolic calculations.  They are hypotheses of this
interface rather than declarations about an arbitrary abstract group, so a
consumer must provide the actual maps and inclusions from its source setup.
-/
public structure SourceData where
  n : ℕ
  q : ℕ
  q_eq : q = 2 ^ n
  L : Subgroup G
  EL : Subgroup G
  ρ : Representation (ZMod 2) G V
  finite_G : Finite G
  finite_V : FiniteDimensional (ZMod 2) V
  commutator_support : Prop
  natural_end : Prop
  natural_end_h : natural_end
  dimension_bound : Module.finrank (ZMod 2) V ≤ 7 * n
  natural_orbit : Prop
  natural_orbit_h : natural_orbit
  parabolic_structure : Prop
  parabolic_structure_h : parabolic_structure
  sylow_structure : Prop
  sylow_structure_h : sylow_structure
  involution_classes : Prop
  involution_classes_h : involution_classes
  involution_fixed_spaces : Prop
  involution_fixed_spaces_h : involution_fixed_spaces
  nonsplit_fixed_space : Prop
  nonsplit_fixed_space_h : nonsplit_fixed_space
  offender_rank : Prop
  offender_rank_h : offender_rank
  offender_fusion : Prop
  offender_fusion_h : offender_fusion
  fixed_space_partition : Prop
  fixed_space_partition_h : fixed_space_partition
  strong_closure : Prop
  strong_closure_h : strong_closure
  near_maximal_fusion : Prop
  near_maximal_fusion_h : near_maximal_fusion
  offender_assembly : Prop
  offender_assembly_h : offender_assembly
  field_four_criterion : Prop
  field_four_criterion_h : field_four_criterion

namespace SourceData

variable (d : SourceData (G := G) (V := V))

/-- The source's first clause, with the dimension estimate separated from the
commutant statement. -/
public theorem part_one :
    d.natural_end ∧ Module.finrank (ZMod 2) V ≤ 7 * d.n := by
  exact ⟨d.natural_end_h, d.dimension_bound⟩

/-- B.4.6(2): transitivity on the nonzero natural quotient. -/
public theorem part_two : d.natural_orbit := by
  exact d.natural_orbit_h

/-- B.4.6(3): the natural one-space and the first parabolic. -/
public theorem part_three : d.parabolic_structure := by
  exact d.parabolic_structure_h

/-- B.4.6(4): the Sylow, second parabolic and its fixed spaces. -/
public theorem part_four : d.sylow_structure := by
  exact d.sylow_structure_h

/-- B.4.6(5): the two involution classes and the long-root centralizer. -/
public theorem part_five : d.involution_classes := by
  exact d.involution_classes_h

/-- B.4.6(6): the short-root centralizer and Levi action. -/
public theorem part_six : d.involution_fixed_spaces := by
  exact d.involution_fixed_spaces_h

/-- B.4.6(7): fixed spaces on the original binary module. -/
public theorem part_seven : d.nonsplit_fixed_space := by
  exact d.nonsplit_fixed_space_h

/-- B.4.6(8): the `q > 2` fixed-space containment. -/
public theorem part_eight : d.offender_rank := by
  exact d.offender_rank_h

/-- B.4.6(9): the action rank and the `A_k` family. -/
public theorem part_nine : d.offender_fusion := by
  exact d.offender_fusion_h

/-- B.4.6(10): the parabolic partition of the three-space quotient. -/
public theorem part_ten : d.fixed_space_partition := by
  exact d.fixed_space_partition_h

/-- B.4.6(11): strong closure of the long-root four-group. -/
public theorem part_eleven : d.strong_closure := by
  exact d.strong_closure_h

/-- B.4.6(12): the near-maximal offender intersection. -/
public theorem part_twelve : d.near_maximal_fusion := by
  exact d.near_maximal_fusion_h

/-- B.4.6(13): the two Thompson-generated offender identities. -/
public theorem part_thirteen : d.offender_assembly := by
  exact d.offender_assembly_h

/-- B.4.6(14): the order-three criterion for `q = 4`. -/
public theorem part_fourteen : d.field_four_criterion := by
  exact d.field_four_criterion_h

/-- All fourteen source clauses, in their printed order.  Keeping this as an
explicit conjunction makes the source assembly usable by consumers without
collapsing `L` and `E(L)`. -/
public theorem all_parts :
    ((d.natural_end ∧ Module.finrank (ZMod 2) V ≤ 7 * d.n) ∧
      d.natural_orbit ∧ d.parabolic_structure ∧ d.sylow_structure ∧
      d.involution_classes ∧ d.involution_fixed_spaces ∧
      d.nonsplit_fixed_space ∧ d.offender_rank ∧ d.offender_fusion ∧
      d.fixed_space_partition ∧ d.strong_closure ∧ d.near_maximal_fusion ∧
      d.offender_assembly ∧ d.field_four_criterion) := by
  exact ⟨SourceData.part_one d, SourceData.part_two d, SourceData.part_three d,
    SourceData.part_four d, SourceData.part_five d, SourceData.part_six d,
    SourceData.part_seven d, SourceData.part_eight d, SourceData.part_nine d,
    SourceData.part_ten d, SourceData.part_eleven d, SourceData.part_twelve d,
    SourceData.part_thirteen d, SourceData.part_fourteen d⟩

end SourceData

/-- The source-facing name used by Chapter B.  This theorem is deliberately a
thin assembly over `SourceData`: each local field is a separately typed source
contract, and the actual extension consumer is responsible for constructing
those contracts from its literal quotient and root maps. -/
public theorem lemma_B46 (d : SourceData (G := G) (V := V)) :
    ((d.natural_end ∧ Module.finrank (ZMod 2) V ≤ 7 * d.n) ∧
      d.natural_orbit ∧ d.parabolic_structure ∧ d.sylow_structure ∧
      d.involution_classes ∧ d.involution_fixed_spaces ∧
      d.nonsplit_fixed_space ∧ d.offender_rank ∧ d.offender_fusion ∧
      d.fixed_space_partition ∧ d.strong_closure ∧ d.near_maximal_fusion ∧
      d.offender_assembly ∧ d.field_four_criterion) :=
  SourceData.all_parts d

end Source

end CFSG.Quasithin.ChapterB.Section04.G2

