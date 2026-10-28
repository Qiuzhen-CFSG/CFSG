module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneCentralizer
public import Theory.LinearAlgebra.BinaryFourFixedSpace
public import Theory.ElementaryAbelian.Injective

/-!
# Orders of the actual HS seed-plane centralizers

The full centralizer of a plane of V lies in M=N_G(V). Its image in the
full automorphism group of V is the pointwise plane stabilizer, of index
42. Thus its index in M is 42 and its order is 256. The count uses the
literal ambient centralizer and the original surjective conjugation action.
Every automorphism of the plane extends to V and is realized inside M.
Comparison with this extension puts the entire plane normalizer in M.

These are consequences of HS1--HS2 preceding Aschbacher--Smith I.4.8,
printed p.418.
-/

public section
open Subgroup MulAction Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims

private theorem pointwise_plane_index {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (W : Subgroup E) (hW : Nat.card W = 4) :
    (fixingSubgroup (MulAut E) (W : Set E)).index = 42 := by
  let U := Additive E
  let L : Submodule (ZMod 2) U := AddSubgroup.toZModSubmodule 2 W.toAddSubgroup
  let e : MulAut E ≃* (U ≃ₗ[ZMod 2] U) := {
    toFun a := { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
    invFun a := MulEquiv.toAdditive.symm a.toAddEquiv
    left_inv := by intro a; ext; rfl
    right_inv := by intro a; ext; rfl
    map_mul' := by intro a b; ext; rfl }
  have hdim : Module.finrank (ZMod 2) U = 3 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    change Nat.card E = _ at hh
    simpa only [hE, Nat.card_zmod, show (2 : ℕ)^3 = 8 from by decide] using hh.symm
  have hdimL : Module.finrank (ZMod 2) L = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := L)
    change Nat.card W = _ at hh
    simpa only [hW, Nat.card_zmod, show (2 : ℕ)^2 = 4 from by decide] using hh.symm
  have he : fixingSubgroup (MulAut E) (W : Set E) =
      (BinaryFourFixedSpace.pointwiseFixer L).comap e.toMonoidHom := by
    ext a
    rw [mem_fixingSubgroup_iff]
    rfl
  rw [he, index_comap_of_surjective _ e.surjective,
    BinaryFourFixedSpace.index_pointwiseFixer, hdimL, hdim]
  norm_num [Fin.prod_univ_succ]

private theorem extend_automorphism {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (W : Subgroup E) (f : MulAut W) :
    ∃ a : MulAut E, ∀ w : W, a w = f w := by
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.of_injective W.subtype W.subtype_injective
  let L : Submodule (ZMod 2) (Additive E) := AddSubgroup.toZModSubmodule 2 W.toAddSubgroup
  let b : L ≃ₗ[ZMod 2] L := { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq b
  refine ⟨MulEquiv.toAdditive.symm g.toAddEquiv, ?_⟩
  intro w
  exact (congrArg Additive.toMul (hg w)).symm

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Every plane in the original seed has full ambient centralizer of order 256. -/
theorem TypeAt.plane_centralizer_card (h : TypeAt z V)
    (W : Subgroup G) (hWV : W ≤ V) (hW4 : Nat.card W = 4) :
    Nat.card (centralizer (W : Set G)) = 256 := by
  let := h.elementary
  let M := normalizer (V : Set G)
  let C := centralizer (W : Set G)
  let B := C.subgroupOf M
  let WV := W.subgroupOf V
  let F := fixingSubgroup (MulAut V) (WV : Set V)
  let f := V.normalizerMonoidHom
  have hCM : C ≤ M := h.plane_centralizer_le_normalizer W hWV hW4
  have hWVcard : Nat.card WV = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWV).toEquiv).trans hW4
  have hiF : F.index = 42 := pointwise_plane_index h.seed_card WV hWVcard
  have hB : B = F.comap f := by
    ext g
    change (g : G) ∈ C ↔ f g ∈ F
    rw [mem_fixingSubgroup_iff]
    constructor
    · intro hg w hw
      apply Subtype.ext
      change (g : G) * (w : G) * (g : G)⁻¹ = w
      rw [← hg w hw, mul_inv_cancel_right]
    · intro hg w hw
      have he := congrArg Subtype.val (hg (⟨w, hWV hw⟩ : V) hw)
      change (g : G) * w * (g : G)⁻¹ = w at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hi : B.index = 42 := by
    rw [hB, index_comap_of_surjective _ h.seed_action_surjective]
    exact hiF
  have hh := B.index_mul_card
  rw [hi, h.normalizer_card,
    Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv] at hh
  change Nat.card C = 256
  omega

/-- The full ambient normalizer of a seed plane preserves the original seed. -/
theorem TypeAt.plane_normalizer_le_seed_normalizer (h : TypeAt z V)
    (W : Subgroup G) (hWV : W ≤ V) (hW4 : Nat.card W = 4) :
    normalizer (W : Set G) ≤ normalizer (V : Set G) := by
  let := h.elementary
  let M := normalizer (V : Set G)
  let WV := W.subgroupOf V
  let e : WV ≃* W := subgroupOfEquivOfLe hWV
  intro g hg
  let b : MulAut WV := e.trans ((W.normalizerMonoidHom ⟨g, hg⟩).trans e.symm)
  obtain ⟨a, ha⟩ := extend_automorphism WV b
  obtain ⟨m, hm⟩ := h.seed_action_surjective a
  have hmatch (w : G) (hw : w ∈ W) :
      (m : G) * w * (m : G)⁻¹ = g * w * g⁻¹ := by
    have he := congrArg (fun v : V => (v : G)) (ha ⟨⟨w, hWV hw⟩, hw⟩)
    rw [← hm] at he
    exact he
  have hc : (m : G)⁻¹ * g ∈ centralizer (W : Set G) := by
    intro w hw
    have he : ((m : G)⁻¹ * g) * w * ((m : G)⁻¹ * g)⁻¹ = w := by
      calc
        _ = (m : G)⁻¹ * (g * w * g⁻¹) * m := by group
        _ = (m : G)⁻¹ * ((m : G) * w * (m : G)⁻¹) * m := by rw [← hmatch w hw]
        _ = w := by group
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hh := M.mul_mem m.property (h.plane_centralizer_le_normalizer W hWV hW4 hc)
  simpa only [mul_inv_cancel_left] using hh

end CFSG.Quasithin.HigmanSims
