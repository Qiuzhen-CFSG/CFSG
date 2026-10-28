module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Selection
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The marked distance-four edge image

The original edge fixed subgroup has index two in the natural eight-group.
Its actual conjugation coordinates therefore give a fixed plane for the
marked edge image. The source edge index and square calculation give order
four and exponent two. On two copies of the natural module, these facts
make that same image an offender.

DistanceFourMovement uses the proved offender catalogue to identify this
image and the original Sylow image with one common flag, then proves the
original radical-centralizer inequality. No independently chosen marking
or extra action premise is introduced.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.5)--(4.6.6), p.903;
Aschbacher--Smith C.1.34(3), printed pp.136--137.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem natural_fixed_iff (common : CommonFacts R source geometry)
    (u : U R (alpha R)) :
    (common.natural.equiv u).toAdd ∈ fixedSpace BinaryLinearThree.W
        (R.map (common.natural.marking.toMonoidHom.comp source.projection)) ↔
      (u : FreeAmalgam R) ∈ centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
  constructor
  · intro hu r hr
    rw [Q_beta] at hr
    obtain ⟨r,hr,rfl⟩ := hr
    let v : U R (alpha R) := (U R (alpha R)).normalizerMonoidHom
      ⟨embedM R r,common.natural.normalized ⟨r,rfl⟩⟩ u
    have hv := common.natural.action r u v rfl
    have hf := hu ⟨common.natural.marking (source.projection r),r,hr,rfl⟩
    have he : v = u := common.natural.equiv.injective
      (Multiplicative.toAdd.injective (hv.trans hf))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  · intro hu a
    obtain ⟨r,hr,he⟩ := a.property
    have hh := common.natural.action r u u (by
      rw [hu (embedM R r) (by rw [Q_beta]; exact mem_map_of_mem _ hr),mul_inv_cancel_right])
    change BinaryLinearThree.W (a : SL) (common.natural.equiv u).toAdd = _
    rw [← he]
    exact hh.symm

/-- The source edge index is the fixed-plane count for the same marked matrix image. -/
theorem marked_edge_fixed_card (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) :
    Nat.card (fixedSpace BinaryLinearThree.W
      (R.map (common.natural.marking.toMonoidHom.comp source.projection))) = 4 := by
  let C := (centralizer (Q R (beta R) : Set (FreeAmalgam R))).subgroupOf (U R (alpha R))
  let f : C ≃ fixedSpace BinaryLinearThree.W
      (R.map (common.natural.marking.toMonoidHom.comp source.projection)) := {
    toFun u := ⟨(common.natural.equiv u).toAdd,(natural_fixed_iff common u).mpr u.property⟩
    invFun v := ⟨common.natural.equiv.symm (Multiplicative.ofAdd (v : BinaryLinearThree.Vector)),
      (natural_fixed_iff common _).mp (by
        rw [MulEquiv.apply_symm_apply]
        exact v.property)⟩
    left_inv u := Subtype.ext (common.natural.equiv.symm_apply_apply u)
    right_inv v := Subtype.ext (congrArg Multiplicative.toAdd
      (common.natural.equiv.apply_symm_apply (Multiplicative.ofAdd (v : BinaryLinearThree.Vector)))) }
  have hC : C = (Z R (beta R)).subgroupOf (U R (alpha R)) := by
    ext u
    change (u : FreeAmalgam R) ∈ centralizer (Q R (beta R) : Set (FreeAmalgam R)) ↔
      (u : FreeAmalgam R) ∈ Z R (beta R)
    rw [Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]
    exact (and_iff_right ((U_le_Z _) u.property)).symm
  have hi : C.index = 2 := by
    rw [hC]
    change (Z R (beta R)).relIndex (U R (alpha R)) = 2
    rw [← Early.edge_Z_index_eq_natural common (alpha R) (beta R) rfl (base_adjacent R)]
    exact early.edge_Z_index _ _ rfl (base_adjacent R)
  have hc := C.card_mul_index
  rw [hi, common.natural.card_at _ rfl] at hc
  rw [← Nat.card_congr f]
  omega

/-- In the natural marking the genuine distance-four replacement image is a
common-axis offender on two copies of the natural module. -/
theorem marked_edge_offender (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) :
    IsOffender (BinaryLinearThree.W.prod BinaryLinearThree.W)
      (R.map (common.natural.marking.toMonoidHom.comp source.projection)) := by
  let E := R.map (common.natural.marking.toMonoidHom.comp source.projection)
  have hc : Nat.card E = 4 := by
    change Nat.card (R.map (common.natural.marking.toMonoidHom.comp source.projection)) = 4
    rw [← map_map, card_map_of_injective common.natural.marking.injective]
    exact Flags.RankOne.edge_image_card source geometry early
  have he : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hc
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      obtain ⟨r,hr,hrx⟩ := x.property
      change (x : SL) ^ 2 = 1
      rw [← hrx]
      change common.natural.marking (source.projection r) ^ 2 = 1
      rw [← map_pow, Flags.RankOne.edge_image_square source geometry common early r hr, map_one]) }
  have hf : Module.finrank (ZMod 2) (fixedSpace BinaryLinearThree.W E) = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace BinaryLinearThree.W E)
    rw [Nat.card_zmod, marked_edge_fixed_card common early] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hh.symm
  change IsOffender (BinaryLinearThree.W.prod BinaryLinearThree.W) E
  refine ⟨⟨?_,he⟩,?_⟩
  · intro hh
    rw [hh] at hc
    have hone : Nat.card (⊥ : Subgroup SL) = 1 := Nat.card_unique
    omega
  · rw [fixedCodim_prod]
    have hh := fixedCodim_add_finrank BinaryLinearThree.W E
    have hd : Module.finrank (ZMod 2) BinaryLinearThree.Vector = 3 := by simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    rw [hf,hd] at hh
    have hr : rank E = 2 := by rw [rank,hc]; decide
    omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour