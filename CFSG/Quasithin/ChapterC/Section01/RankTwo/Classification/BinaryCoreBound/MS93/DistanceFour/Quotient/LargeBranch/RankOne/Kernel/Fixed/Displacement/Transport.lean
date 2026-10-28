module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Kernel.Fixed.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Assembly

/-!
# Exact fixed-space transport on the actual core quotient

The finite action `SmallBranch.QuotientAction` has kernel exactly U_alpha and
uses literal conjugation through the original source projection. For each of
the two intrinsic parabolic two-cores, its fixed-space preimage is precisely
the ambient commutator preimage. Surjectivity identifies its index with the
power of two determined by the fixed codimension. The image actor is the
actual model parabolic two-core, elementary of order four.

The full invariant preimage is core intersect Z_alpha. Consequently the
starred index 64 bounds the quotient by the invariant space by dimension six;
it does not bound the dimension of core/U_alpha itself. These results do not
assert the missing existence of a flag with fixed codimension at most two.

Source: Meierfrankenfeld--Stellmacher (1993), (1.4), p.842, and the quotient
conventions in (4.6.12), pp.910--912. The requested whole-core estimate is a
separate sufficient route, not a displayed inequality in (4.6.12).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Fixed.Displacement
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)
  (d : SmallBranch.QuotientAction source)

omit [Finite M] in
/-- A vector is fixed precisely when its literal conjugation displacement lies in U. -/
theorem fixed_iff_commutator_mem (m : M) (x : core R (alpha R)) :
    d.representation (source.projection m) (d.projection x).toAdd = (d.projection x).toAdd ↔
      ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ U R (alpha R) := by
  let y := coreAction (R := R) m x
  rw [← d.action m x y rfl]
  have he : (d.projection y).toAdd = (d.projection x).toAdd ↔
      y * x⁻¹ ∈ d.projection.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    exact Multiplicative.toAdd.injective.eq_iff
  rw [he, d.kernel]
  rfl

include common in
/-- The entire fixed-space preimage equals the ambient commutator preimage, in both directions. -/
theorem fixed_preimage_eq (i : Bool) :
    (commutatorPreimage (core R (alpha R)) (Flags.RankOne.flagKernel source i)
      (U R (alpha R))).subgroupOf (core R (alpha R)) =
    ((fixedSpace d.representation
      (((parabolic source.projection source.flag i).pCoreIn 2).map source.projection)).toAddSubgroup.toSubgroup).comap
        d.projection := by
  let C := core R (alpha R)
  let P := (parabolic source.projection source.flag i).pCoreIn 2
  let A := P.map source.projection
  let K := commutatorPreimage C (Flags.RankOne.flagKernel source i) (U R (alpha R))
  let W := fixedSpace d.representation A
  let H : Subgroup (Multiplicative d.Space) := W.toAddSubgroup.toSubgroup
  let F : Subgroup C := H.comap d.projection
  change K.subgroupOf C = F
  have hC : C ≤ stabilizer R (alpha R) := (core_le_Q source).trans (fun _ hx => hx.1)
  have hKU : ⁅K, Flags.RankOne.flagKernel source i⁆ ≤ U R (alpha R) :=
    commutator_commutatorPreimage_le _ _ _
      (hC.trans (by rw [alpha, stabilizer_m_base]; exact common.natural.normalized))
  apply le_antisymm
  · intro x hx
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
  · have hFK : F.map C.subtype ≤ K := by
      apply le_commutatorPreimage (map_subtype_le F)
      rw [commutator_comm]
      apply commutator_le.mpr
      rintro p ⟨m, hm, rfl⟩ x ⟨c, hc, rfl⟩
      let y := coreAction (R := R) m c
      have hfix : d.representation (source.projection m) (d.projection c).toAdd =
          (d.projection c).toAdd := hc ⟨source.projection m, mem_map_of_mem _ hm⟩
      have hq : d.projection y = d.projection c :=
        Multiplicative.toAdd.injective ((d.action m c y rfl).trans hfix)
      have hz : y * c⁻¹ ∈ d.projection.ker := by
        change d.projection (y * c⁻¹) = 1
        rw [map_mul, map_inv, hq, mul_inv_cancel]
      rwa [d.kernel] at hz
    intro x hx
    exact hFK (mem_map_of_mem C.subtype hx)


include common in
/-- The actual fixed-preimage index is exactly the binary power of the fixed codimension. -/
theorem fixed_preimage_index (i : Bool) :
    (commutatorPreimage (core R (alpha R)) (Flags.RankOne.flagKernel source i)
      (U R (alpha R))).relIndex (core R (alpha R)) =
      2 ^ fixedCodim d.representation
        (((parabolic source.projection source.flag i).pCoreIn 2).map source.projection) := by
  change ((commutatorPreimage _ _ _).subgroupOf _).index = _
  rw [fixed_preimage_eq source common d i,
    Subgroup.index_comap_of_surjective _ d.onto, AddSubgroup.index_toSubgroup]
  change Nat.card (d.Space ⧸ fixedSpace d.representation _) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rfl

include common in
/-- The desired index estimate is equivalent to the codimension estimate for the same actor. -/
theorem flag_index_le_four_iff (i : Bool) :
    (commutatorPreimage (core R (alpha R)) (Flags.RankOne.flagKernel source i)
      (U R (alpha R))).relIndex (core R (alpha R)) ≤ 4 ↔
      fixedCodim d.representation
        (((parabolic source.projection source.flag i).pCoreIn 2).map source.projection) ≤ 2 := by
  rw [fixed_preimage_index source common d i]
  change 2 ^ _ ≤ 2 ^ 2 ↔ _
  exact pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))

/-- The original projection carries the intrinsic parabolic core onto the marked model core. -/
theorem flag_actor_eq_model_core (i : Bool) :
    ((parabolic source.projection source.flag i).pCoreIn 2).map source.projection =
      (modelParabolic source.flag i).pCoreIn 2 := by
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  rw [map_pCoreIn_of_ker_isPGroup source.projection hk,
    show (parabolic source.projection source.flag i).map source.projection =
      modelParabolic source.flag i from
        map_comap_eq_self_of_surjective source.projection_surjective _]

/-- The actual image actor is elementary abelian of order four. -/
theorem flag_actor_data (i : Bool) :
    IsElementaryAbelian 2
      (((parabolic source.projection source.flag i).pCoreIn 2).map source.projection) ∧
    Nat.card (((parabolic source.projection source.flag i).pCoreIn 2).map
      source.projection) = 4 := by
  rw [flag_actor_eq_model_core source i]
  let P := modelParabolic source.flag i
  let e := (pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective
  have hd := Matrix.PSL3Two.ParabolicCoreModel.core_data
    (modelParabolicEquivSymmetric source.flag i)
  let : IsElementaryAbelian 2 (pCore 2 P) := hd.1
  exact ⟨IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective,
    (Nat.card_congr e.toEquiv.symm).trans hd.2⟩


include common in
/-- The full fixed-space preimage is the relative Z-layer; no equality of Z and U is used. -/
theorem invariant_preimage_eq (radius : RadiusFacts R geometry) :
    ((fixedSpace d.representation ⊤).toAddSubgroup.toSubgroup).comap d.projection =
      (Z R (alpha R)).subgroupOf (core R (alpha R)) := by
  ext x
  constructor
  · intro hx
    apply SmallBranch.core_inter_B_le_Z source geometry common radius (alpha R) (beta R)
      rfl (base_adjacent R)
    refine ⟨x.property, ?_⟩
    apply (mem_B_iff R (alpha R) (geometry.Z_normal _)
      (geometry.V_local _ rfl common.large_distance) x).mpr
    refine ⟨radius.core_le_radius _ rfl x.property, ?_⟩
    intro l hl
    rw [Ltilde_alpha] at hl
    obtain ⟨m, _hm, rfl⟩ := hl
    apply DistanceEight.U_le_Z R (alpha R)
    exact (fixed_iff_commutator_mem source d m x).mp
      (hx ⟨source.projection m, mem_top _⟩)
  · intro hx g
    obtain ⟨m, hm⟩ := source.projection_surjective g.val
    change d.representation g.val (d.projection x).toAdd = (d.projection x).toAdd
    rw [← hm]
    apply (fixed_iff_commutator_mem source d m x).mpr
    have hc := Flags.RankOne.Z_stabilizer_commutator_le_U source geometry common
    rw [commutator_comm] at hc
    apply hc (commutator_mem_commutator _ hx)
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩

include common in
/-- The quotient by the fixed space has the exact index of the core intersection with Z. -/
theorem invariant_quotient_card (radius : RadiusFacts R geometry) :
    Nat.card (d.Space ⧸ fixedSpace d.representation ⊤) =
      (Z R (alpha R)).relIndex (core R (alpha R)) := by
  change _ = ((Z R (alpha R)).subgroupOf (core R (alpha R))).index
  rw [← invariant_preimage_eq source common d radius,
    Subgroup.index_comap_of_surjective _ d.onto, AddSubgroup.index_toSubgroup]
  rfl

include common in
/-- The starred index bounds dimension only after taking the quotient by the full fixed space. -/
theorem invariant_quotient_finrank_le_six (radius : RadiusFacts R geometry)
    (hindex : (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) = 64) :
    Module.finrank (ZMod 2) (d.Space ⧸ fixedSpace d.representation ⊤) ≤ 6 := by
  have hb : Nat.card (d.Space ⧸ fixedSpace d.representation ⊤) ≤ 64 := by
    rw [invariant_quotient_card source common d radius]
    exact (relIndex_le_of_le_right
      (SmallBranch.core_le_star source geometry common radius (alpha R) (beta R) rfl (base_adjacent R))
      (by rw [hindex]; decide)).trans_eq hindex
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hb
  change 2 ^ _ ≤ 2 ^ 6 at hb
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hb

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Fixed.Displacement
