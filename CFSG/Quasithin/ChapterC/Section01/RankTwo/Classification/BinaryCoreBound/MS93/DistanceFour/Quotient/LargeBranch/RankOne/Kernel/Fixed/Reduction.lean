module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Requirements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Descent
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry.FixedElement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import Theory.GroupTheory.PCoreImage

/-!
# A sufficient rank-one displacement bound for the moving kernel

Use the intrinsic two-core of either of the two marked parabolics, acting on
core/U by actual conjugation. If its fixed preimage has index at most four,
its elementary order-four image in SL3(2) is an offender. The checked binary
FF theorem and the geometric square argument then remove the fixed part of
core/U. In particular the moving span meets the fixed part of Z trivially.

`FlagCoreBound` is an additional geometric obligation, not a constructor from
LocalSource, CommonFacts or RadiusFacts. In particular the index on core/U
cannot be replaced by one on the starred quotient by Z. This module proves
only the reduction from that obligation; it does not prove MovingKernelControl.

Source: original MS93 (1993), (1.4)--(1.5), printed pp.842--843, and
(4.6.12)(1)--(5), pp.910--912. The FF route is a sufficient alternative to
lifting the printed chief-factor argument through the fixed part of Z.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
namespace Fixed

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- A bound for an actual marked parabolic core, on core/U rather than VStar/Z.
Its construction in the large-intersection branch remains a source obligation. -/
def FlagCoreBound (source : LocalSource L R) : Prop :=
  ∃ i : Bool,
    (commutatorPreimage (core R (alpha R)) (Flags.RankOne.flagKernel source i)
      (U R (alpha R))).relIndex (core R (alpha R)) ≤ 4

variable [Finite M] (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

private theorem flag_image_data (i : Bool) :
    IsElementaryAbelian 2
      (((parabolic source.projection source.flag i).pCoreIn 2).map source.projection) ∧
    Nat.card (((parabolic source.projection source.flag i).pCoreIn 2).map
      source.projection) = 4 := by
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  rw [map_pCoreIn_of_ker_isPGroup source.projection hk,
    show (parabolic source.projection source.flag i).map source.projection =
      modelParabolic source.flag i from
        map_comap_eq_self_of_surjective source.projection_surjective _]
  let P := modelParabolic source.flag i
  let e := (pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective
  have hd := Matrix.PSL3Two.ParabolicCoreModel.core_data
    (modelParabolicEquivSymmetric source.flag i)
  let : IsElementaryAbelian 2 (pCore 2 P) := hd.1
  exact ⟨IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective,
    (Nat.card_congr e.toEquiv.symm).trans hd.2⟩

include common in
/-- The literal parabolic fixed-preimage index gives an offender on the
constructed core quotient, retaining the source projection and actual actor. -/
theorem core_offending_of_flag_index (d : SmallBranch.QuotientAction source)
    (i : Bool)
    (hindex : (commutatorPreimage (core R (alpha R))
      (Flags.RankOne.flagKernel source i) (U R (alpha R))).relIndex
        (core R (alpha R)) ≤ 4) : IsFFModule d.representation := by
  let C := core R (alpha R)
  let P := (parabolic source.projection source.flag i).pCoreIn 2
  let A := P.map source.projection
  let K := commutatorPreimage C (Flags.RankOne.flagKernel source i) (U R (alpha R))
  let W := fixedSpace d.representation A
  let H : Subgroup (Multiplicative d.Space) := W.toAddSubgroup.toSubgroup
  let F : Subgroup C := H.comap d.projection
  obtain ⟨hA, hcard⟩ := flag_image_data source i
  have hC : C ≤ stabilizer R (alpha R) := (core_le_Q source).trans (fun _ hx => hx.1)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite C := Finite.of_injective (inclusion hC) (inclusion_injective hC)
  have hKU : ⁅K, Flags.RankOne.flagKernel source i⁆ ≤ U R (alpha R) :=
    commutator_commutatorPreimage_le _ _ _
      (hC.trans (by rw [alpha, stabilizer_m_base]; exact common.natural.normalized))
  have hKF : K.subgroupOf C ≤ F := by
    intro x hx
    change ∀ g : A, d.representation g.val (d.projection x).toAdd = (d.projection x).toAdd
    intro g
    obtain ⟨m, hm, hmg⟩ := g.property
    have hma : embedM R m ∈ Flags.RankOne.flagKernel source i := mem_map_of_mem _ hm
    rw [← hmg]
    let y := coreAction (R := R) m x
    have hz : y * x⁻¹ ∈ d.projection.ker := by
      rw [d.kernel]
      change ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ U R (alpha R)
      rw [commutator_comm] at hKU
      exact hKU (commutator_mem_commutator hma hx)
    have hq : d.projection y = d.projection x := by
      change d.projection (y * x⁻¹) = 1 at hz
      rwa [map_mul, map_inv, mul_inv_eq_one] at hz
    rw [← d.action m x y rfl, hq]
  have hind : F.index ≤ 4 := (Subgroup.index_antitone hKF).trans hindex
  have hpow : 2 ^ fixedCodim d.representation A ≤ 4 := by
    rw [Subgroup.index_comap_of_surjective _ d.onto, AddSubgroup.index_toSubgroup] at hind
    change Nat.card (d.Space ⧸ W) ≤ 4 at hind
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hind
    exact hind
  refine ⟨A, ⟨?_, hA⟩, ?_⟩
  · intro he
    change Nat.card A = 4 at hcard
    rw [he, Subgroup.card_bot] at hcard
    omega
  · have hdim : fixedCodim d.representation A ≤ 2 :=
      (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hpow
    simpa only [rank, show Nat.card A = 4 from hcard, show Nat.log 2 4 = 2 by decide]
      using hdim

include common in
/-- The rank-one index bound eliminates the core's entire extra intersection
with Z. No core order or center equality is assumed. -/
theorem core_inter_Z_eq_U_of_flag_bound (radius : RadiusFacts R geometry)
    (h : FlagCoreBound source) : core R (alpha R) ⊓ Z R (alpha R) = U R (alpha R) := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨d⟩ := SmallBranch.exists_quotientAction source geometry common radius
  let c : SmallBranch.CoreModule source := {
    Space := d.Space
    representation := d.representation
    projection := d.projection
    onto := d.onto
    kernel := d.kernel
    action := d.action
    faithful := d.faithful common radius
    full := d.full
    offending := core_offending_of_flag_index source common d i hi }
  obtain ⟨m, _, ⟨q⟩⟩ := AbelianCore.QuotientRecognition.ExtensionControl.exists_moduleQuotient
    c.representation c.faithful c.full c.offending
  exact SmallBranch.core_inter_Z_eq_U source geometry common radius c m q

include common in
/-- At a distance-two vertex the canonical moving subgroup has no fixed
kernel once the actual parabolic displacement bound has been supplied. -/
theorem moving_fixed_eq_bot_of_flag_bound (radius : RadiusFacts R geometry)
    (h : FlagCoreBound source) (c : Vertex R)
    (hd : (cosetGraph R).dist (alpha R) c = 2) :
    movingSpan c ⊓ (Z R (alpha R) ⊓
      centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hu : x ∈ U R (alpha R) := by
    rw [← core_inter_Z_eq_U_of_flag_bound source common radius h]
    exact ⟨movingSpan_le_core geometry common.large_distance c hd hx.1, hx.2.1⟩
  exact (disjoint_iff.mp common.disjoint).le ⟨hu, hx.2⟩

end Fixed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
