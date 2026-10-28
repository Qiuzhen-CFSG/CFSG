module

public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed
public import CFSG.Quasithin.ChapterE.Section03.Parameters.FourDimensional

/-!
# The fixed plane when the Thompson image has order two

On a prepared four-dimensional binary module, quadratic ratio two excludes
FF offenders. An involution therefore has fixed codimension two. Identify
the fixed space of the actual action image with the ambient subgroup
`C_V(J₁(T))` to obtain its order, without replacing either action map.

This is a local calculation for the exceptional alternative of original
15.1.13(4b). It does not assert the global normalization in 15.1.14.

Source: Aschbacher--Smith, 15.1.13--14, printed pp.1090--1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private noncomputable def fixedSpaceEquiv
    (M V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (hAM : A ≤ M) :
    (V ⊓ centralizer (A : Set G) : Subgroup G) ≃
      fixedSpace (imageRepresentation M V hn)
        ((A.subgroupOf M).map (actionHom M V hn).rangeRestrict) where
  toFun v := ⟨Additive.ofMul ⟨v, v.property.1⟩, by
    rintro ⟨_, a, ha, rfl⟩
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (a : G) * (v : G) * (a : G)⁻¹ = v
    rw [v.property.2 a ha, mul_inv_cancel_right]⟩
  invFun v := ⟨v.val.toMul, v.val.toMul.property, by
    intro a ha
    have hv := v.property ⟨_, mem_map_of_mem (actionHom M V hn).rangeRestrict
      (show (⟨a, hAM ha⟩ : M) ∈ A.subgroupOf M from ha)⟩
    have he := congrArg (fun w : Additive V => (w.toMul : G)) hv
    change a * (v.val.toMul : G) * a⁻¹ = v.val.toMul at he
    exact mul_inv_eq_iff_eq_mul.mp he⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The order-two Thompson action on a prepared binary four-space fixes a plane. -/
theorem PreparedChosenModule.thompsonFixed_card_of_image_two
    (T : Sylow 2 G) {M V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 4)
    (htwo : Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict) = 2) :
    Nat.card (thompsonFixed T V) = 4 := by
  classical
  let := h.elementary
  let f : M →* internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict
  let A := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let : IsCyclic A := isCyclic_of_prime_card htwo
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  have ha2 : orderOf a.val = 2 := (Subgroup.orderOf_coe a).trans (ha.trans htwo)
  have hA : zpowers a.val = A := by
    have hg : zpowers a = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp (by
      rw [Nat.card_zpowers, ha])
    have he := congrArg (Subgroup.map A.subtype) hg
    simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype,
      ← MonoidHom.range_eq_map, range_subtype] using he
  have hn : ¬ IsFFModule (imageRepresentation M V h.normalized) := by
    intro hh
    have hb := (isFFModule_iff_quadraticRatio_le_one _).mp hh
    rw [h.quadratic_ratio] at hb
    norm_num at hb
  have hc := ChapterE.involution_fixedCodim_eq_two_of_four_nonFF
    (imageRepresentation M V h.normalized) hdim.le hn a.val ha2
  have hd := fixedCodim_add_finrank (imageRepresentation M V h.normalized) (zpowers a.val)
  rw [hc, hdim, hA] at hd
  have hf : Module.finrank (ZMod 2)
      (fixedSpace (imageRepresentation M V h.normalized) A) = 2 := by omega
  rw [Nat.card_congr (fixedSpaceEquiv M V (ChapterB.thompsonJ (T : Subgroup G) 1)
    h.normalized ((ChapterB.thompsonJ_le _ _).trans hTM)),
    Module.natCard_eq_pow_finrank (K := ZMod 2), hf, Nat.card_zmod]
  norm_num

end CFSG.Quasithin.Chapter15.Section01
