module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMovingCore
public import Theory.GroupAction.FourthPowerFixedCard

/-!
# The order-eight displacement of the original cyclic-four action

On an elementary binary group of order sixteen, a fourth-power-one
actor whose square fixes exactly four points fixes exactly two points.
Its cyclic commutator therefore has order eight. The proof uses the
strict fixed-point increase under squaring and the fourth-root bound,
then identifies the literal displacement homomorphism with the cyclic
commutator. No choice of coordinates or replacement module is involved.

Source: the cyclic-four local action in Aschbacher--Smith 15.1.2(5)
and 15.1.14, printed pp.1086 and 1091.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.NineAction
variable {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]

/-- The generator of the cyclic-four action fixes a line and moves a hyperplane. -/
theorem fourth_power_fixed_displacement
    (a : MulAut W) (ha4 : a ^ 4 = 1) (hW : Nat.card W = 16)
    (hF2 : Nat.card (FixedPoints.subgroup (zpowers (a ^ 2)) W) = 4) :
    Nat.card (FixedPoints.subgroup (zpowers a) W) = 2 ∧
      ∃ d : W →* W, (∀ w, d w = w⁻¹ * a w) ∧
        d.range = commutatorAction (zpowers a) W ∧ Nat.card d.range = 8 := by
  have hane : a ≠ 1 := by
    intro he
    have htop : FixedPoints.subgroup (zpowers (a ^ 2)) W = ⊤ := by
      ext w
      rw [MulAut.mem_fixed_zpowers_iff]
      simp [he]
    rw [htop,card_top,hW] at hF2
    omega
  let F := FixedPoints.subgroup (zpowers a) W
  have hlt : Nat.card F < 4 := by
    simpa only [hF2] using
      a.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one ha4 hane
  have hlarge : 1 < Nat.card F := by
    have hh := a.card_le_fixed_card_pow_four_of_fourth_power_eq_one ha4
    change Nat.card W ≤ Nat.card F ^ 4 at hh
    rw [hW] at hh
    by_contra hn
    have hle : Nat.card F ^ 4 ≤ 1 :=
      (Nat.pow_le_pow_left (show Nat.card F ≤ 1 by omega) 4).trans (by decide)
    omega
  have hdiv : Nat.card F ∣ 16 := hW ▸ F.card_subgroup_dvd_card
  have hnot3 : Nat.card F ≠ 3 := by intro he; rw [he] at hdiv; norm_num at hdiv
  have hF : Nat.card F = 2 := by omega
  let d : W →* W := {
    toFun := fun w => w⁻¹ * a w
    map_one' := by simp
    map_mul' := by intros; simp only [map_mul,mul_inv_rev]; ac_rfl }
  have hd (w : W) : d w = w⁻¹ * a w := rfl
  have hker : d.ker = F := by
    ext w
    rw [MonoidHom.mem_ker,MulAut.mem_fixed_zpowers_iff,hd,inv_mul_eq_one,eq_comm]
  have hrange : d.range = commutatorAction (zpowers a) W := by
    apply le_antisymm
    · rintro _ ⟨w,rfl⟩
      rw [commutatorAction_eq_closure]
      exact subset_closure ⟨⟨a,mem_zpowers a⟩,w,rfl⟩
    · let K : Subgroup (MulAut W) := {
        carrier := {b | ∀ w : W, w⁻¹ * b w ∈ d.range}
        one_mem' := by intro w; simp
        mul_mem' := by
          intro b c hb hc w
          have hh := d.range.mul_mem (hc w) (hb (c w))
          change w⁻¹ * b (c w) ∈ d.range
          simpa only [mul_assoc,mul_inv_cancel_left] using hh
        inv_mem' := by
          intro b hb w
          have hh := d.range.inv_mem (hb (b⁻¹ w))
          simpa only [MulAut.apply_inv_self,mul_inv_rev,inv_inv] using hh }
      have hK : zpowers a ≤ K := zpowers_le.mpr (fun w => ⟨w,rfl⟩)
      rw [commutatorAction_eq_closure,closure_le]
      rintro _ ⟨b,w,rfl⟩
      exact hK b.property w
  refine ⟨hF,d,hd,hrange,?_⟩
  have hh := d.ker.card_mul_index
  rw [index_ker,hker,hF,hW] at hh
  omega

end CFSG.Quasithin.Chapter15.Section01.NineAction

namespace CFSG.Quasithin.Chapter15.Section01
open Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup inducing the whole cyclic-four Nine action moves at least
an order-eight subgroup of the original prepared module. -/
theorem PreparedChosenModule.nine_commutator_card_ge_eight_of_full_image
    (T : Sylow 2 G) {M V Q : Subgroup G}
    (hp : PreparedChosenModule T M V)
    (h9 : letI := hp.elementary
      SourceCases.Nine (imageRepresentation M V hp.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict))
    (himage : (Q.subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict) :
    8 ≤ Nat.card (⁅V,Q⁆ : Subgroup G) := by
  classical
  let := hp.elementary
  let D := internalActionImage M V hp.normalized
  let ρ := imageRepresentation M V hp.normalized
  let f : M →* D := (actionHom M V hp.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  obtain ⟨_,_,hdim,_,_,_,hS,_⟩ := h9
  let : IsCyclic S := hS.1
  obtain ⟨s,hs⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hs4 : orderOf (s : D) = 4 :=
    (Subgroup.orderOf_coe s).trans (hs.trans hS.2)
  let a : MulAut V := (s : D).val
  have ha4 : a ^ 4 = 1 := congrArg Subtype.val (hs4 ▸ pow_orderOf_eq_one (s : D))
  have hW : Nat.card V = 16 := by
    change Nat.card (Additive V) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hdim,Nat.card_zmod]
    norm_num
  have hs2 : orderOf ((s : D) ^ 2) = 2 := by rw [orderOf_pow,hs4]; decide
  have hnon : ¬ IsFFModule ρ := by
    intro hff
    have hh := (isFFModule_iff_quadraticRatio_le_one ρ).mp hff
    rw [hp.quadratic_ratio] at hh
    norm_num at hh
  have hc := ChapterE.involution_fixedCodim_eq_two_of_four_nonFF ρ hdim.le hnon
    ((s : D) ^ 2) hs2
  have hrank := fixedCodim_add_finrank ρ (zpowers ((s : D) ^ 2))
  rw [hc,hdim] at hrank
  have hF2rank : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers ((s : D) ^ 2))) = 2 := by
    omega
  let e : FixedPoints.subgroup (zpowers (a ^ 2)) V ≃
      fixedSpace ρ (zpowers ((s : D) ^ 2)) := {
    toFun := fun v => ⟨Additive.ofMul v.val, by
      rw [mem_fixedSpace_zpowers_iff]
      exact congrArg Additive.ofMul ((MulAut.mem_fixed_zpowers_iff _ _).mp v.property)⟩
    invFun := fun v => ⟨v.val.toMul, by
      rw [MulAut.mem_fixed_zpowers_iff]
      exact congrArg Additive.toMul ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hF2 : Nat.card (FixedPoints.subgroup (zpowers (a ^ 2)) V) = 4 := by
    rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod 2),hF2rank,Nat.card_zmod]
    norm_num
  obtain ⟨_,d,hd,_,hdcard⟩ := NineAction.fourth_power_fixed_displacement a ha4 hW hF2
  have hsQ : (s : D) ∈ (Q.subgroupOf M).map f := himage.symm ▸ s.property
  obtain ⟨q,hq,he⟩ := hsQ
  have hle : d.range.map V.subtype ≤ ⁅V,Q⁆ := by
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    have heval : (a v : G) = (q : G) * (v : G) * (q : G)⁻¹ := by
      have hh := congrArg (fun b : D => ((b.val v : V) : G)) he
      exact hh.symm
    change (d v : G) ∈ ⁅V,Q⁆
    rw [hd]
    change (v : G)⁻¹ * (a v : G) ∈ ⁅V,Q⁆
    rw [heval]
    have hh := commutator_mem_commutator (V.inv_mem v.property) hq
    simpa only [commutatorElement_def,inv_inv,mul_assoc,Subgroup.coe_subtype] using hh
  have hh := card_le_of_le hle
  rw [card_map_of_injective V.subtype_injective,hdcard] at hh
  exact hh


/-- Mutual normalization and full Nine action leave at most a two-element
image of the original module modulo the actor subgroup. -/
theorem PreparedChosenModule.nine_relIndex_le_two_of_full_image
    (T : Sylow 2 G) {M V Q : Subgroup G}
    (hp : PreparedChosenModule T M V)
    (h9 : letI := hp.elementary
      SourceCases.Nine (imageRepresentation M V hp.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict))
    (hQM : Q ≤ M) (hVQ : V ≤ normalizer (Q : Set G))
    (himage : (Q.subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict) :
    Q.relIndex V ≤ 2 := by
  have hc := hp.nine_commutator_card_ge_eight_of_full_image T h9 himage
  have hle : ⁅V,Q⁆ ≤ Q ⊓ V := le_inf
    (le_normalizer_iff_commutator_le_right.mp hVQ)
    (le_normalizer_iff_commutator_le_left.mp (hQM.trans hp.normalized))
  have hlo : 8 ≤ Nat.card (Q ⊓ V : Subgroup G) := hc.trans (card_le_of_le hle)
  let := hp.elementary
  have hdim : Module.finrank (ZMod 2) (Additive V) = 4 := h9.choose_spec.2.1
  have hW : Nat.card V = 16 := by
    change Nat.card (Additive V) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hdim,Nat.card_zmod]
    norm_num
  have hh := ((Q ⊓ V).subgroupOf V).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show Q ⊓ V ≤ V from inf_le_right)).toEquiv] at hh
  change Nat.card (Q ⊓ V : Subgroup G) * (Q ⊓ V).relIndex V = Nat.card V at hh
  rw [inf_relIndex_right,hW] at hh
  nlinarith

end CFSG.Quasithin.Chapter15.Section01
