module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
import Mathlib.Tactic.FinCases

/-!
# The full Mathieu row normalizer

The 21-point rectangle quotient realizes the binary coordinate interchange
which swaps the first and third columns. It moves the distinguished root and
preserves the first row. The literal row-plane normalizer identity puts this
element in N_G(U₁). Source 39.3 then gives the full natural four-space action
and its splitting, with the original quotient map and coordinates retained.

Source: Aschbacher, *Sporadic Groups* (1994), 40.3 and 40.5(2), pp.217–219.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code pure rankOneGroup)

private def swapColumns (x : Code) : Code :=
  (x &&& 18) ||| ((x &&& 9) <<< 2) ||| ((x &&& 36) >>> 2)
private theorem swapColumns_square : ∀ x : Code, swapColumns (swapColumns x) = x := by decide
private def columnSwap : Equiv.Perm Code :=
  ⟨swapColumns, swapColumns, swapColumns_square, swapColumns_square⟩
private theorem columnSwap_rankOne : columnSwap ∈ rankOneGroup := by
  apply (PlaneCensus.mem_rankOneGroup _).mpr
  exact ⟨by decide, by decide⟩
private theorem columnSwap_row : ∀ x : Code, x >>> 3 = 0 → columnSwap x >>> 3 = 0 := by decide
private theorem columnSwap_point : columnSwap 4 = 1 := by decide

private theorem model_mem_row_iff (v : Six) :
    (modelPlaneCoordinates.symm (Multiplicative.ofAdd v) : SL) ∈ Model.row ↔ v 1 = 0 := by
  let g := modelPlaneCoordinates.symm (Multiplicative.ofAdd v)
  have hm := modelPlaneCoordinates_matrix g
  have hc : modelPlaneCoordinates g = Multiplicative.ofAdd v := modelPlaneCoordinates.apply_symm_apply _
  rw [hc] at hm
  simp only [toAdd_ofAdd] at hm
  constructor
  · intro hg
    have hr := modelRowCoordinates_matrix ⟨(g : SL), hg⟩
    funext j
    have he := congrArg (fun A : Matrix (Fin 5) (Fin 5) (ZMod 2) => A 1 (j.natAdd 2)) (hm.symm.trans hr)
    fin_cases j <;> simpa [Matrix.single] using he
  · intro hv
    let w : Multiplicative (Fin 4 → ZMod 2) := Multiplicative.ofAdd ![0,v 0 0,v 0 1,v 0 2]
    have he : (g : SL) = (modelRowCoordinates.symm w : SL) := by
      apply Subtype.ext
      rw [hm, modelRowCoordinates_matrix, modelRowCoordinates.apply_symm_apply]
      have h0 : v 1 0 = 0 := congrFun hv 0
      have h1 : v 1 1 = 0 := congrFun hv 1
      have h2 : v 1 2 = 0 := congrFun hv 2
      simp [w, h0, h1, h2]
    rw [he]
    exact (modelRowCoordinates.symm w).property

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)
theorem plane_element_mem_row_iff (x : Code) : element F x ∈ F.row ↔ x >>> 3 = 0 := by
  have hc := F.pullback_le _ (element_mem F x)
  rw [F.mem_pullback_iff Model.row ⟨element F x, hc⟩, element_model, model_mem_row_iff]
  exact decode_secondRow_zero_iff x


/-- The 21-point rectangle supplies an ambient element that moves z and
preserves the literal marked row-plane intersection. -/
theorem row_point_mover [Finite G] (hcount : (F.fusion F.plane).ncard = 21) :
    ∃ g : rowNormalizer F, (g : G) * z * (g : G)⁻¹ ≠ z := by
  have hf : columnSwap ∈ (quotientCodeAction F).range := by
    rw [planeCodeAction_range F hcount]
    exact columnSwap_rankOne
  obtain ⟨q, hq⟩ := hf
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  rw [quotientCodeAction_mk] at hq
  have hn : (n : G) ∈ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha.2⟩
      have hxe : element F x = a := congrArg Subtype.val hx
      have hr : x >>> 3 = 0 := (plane_element_mem_row_iff F x).mp (hxe.symm ▸ ha.1)
      have hh : normalizerAction F n x >>> 3 = 0 := by rw [hq]; exact columnSwap_row x hr
      have hmem := (plane_element_mem_row_iff F _).mpr hh
      rw [normalizerAction_element, hxe] at hmem
      exact ⟨hmem, (mem_normalizer_iff.mp n.property a).mp ha.2⟩
    · rw [card_map_of_injective (MulAut.conj (n : G)).injective]
  rw [source_row_plane_normalizer] at hn
  refine ⟨⟨n, hn.1⟩, ?_⟩
  have hm : (n : G) * z * (n : G)⁻¹ = element F 1 := by
    have hh := normalizerAction_element F n 4
    rw [element_point, hq, columnSwap_point] at hh
    exact hh.symm
  exact hm ▸ element_one_ne_point F

/-- The literal row normalizer is larger than the point centralizer. -/
theorem row_normalizer_ne [Finite G] (hcount : (F.fusion F.plane).ncard = 21) :
    rowNormalizer F ≠ Subgroup.centralizer ({z} : Set G) := by
  intro he
  obtain ⟨g, hg⟩ := row_point_mover F hcount
  have hc : (g : G) ∈ Subgroup.centralizer ({z} : Set G) := he ▸ g.property
  exact hg (by rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right])

/-- The source row quotient is the full binary four-space group. -/
def rowQuotientEquiv [Finite G] (hcount : (F.fusion F.plane).ncard = 21) :
    rowQuotient F ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
  (MulEquiv.ofBijective (rowQuotientAction F) ⟨rowQuotientAction_injective F, by
    intro a
    obtain ⟨g, hg⟩ := row_action_surjective_of_normalizer_ne_centralizer F
      (row_normalizer_ne F hcount) a
    refine ⟨QuotientGroup.mk g, ?_⟩
    rw [← hg]
    ext x
    exact rowQuotientAction_mk_apply F g x⟩).trans (rowAutLinearEquiv F)

/-- Its action is the original conjugation action in the marked coordinates. -/
theorem rowQuotientEquiv_action [Finite G] (hcount : (F.fusion F.plane).ncard = 21)
    (g : rowNormalizer F) (x : F.row) :
    rowQuotientEquiv F hcount (QuotientGroup.mk g) (rowCoordinates F x).toAdd =
      (rowCoordinates F (F.row.normalizerMonoidHom g x)).toAdd := by
  change rowAutLinearEquiv F (rowQuotientAction F (QuotientGroup.mk g))
    (rowCoordinates F x).toAdd = _
  rw [rowAutLinearEquiv_apply]
  congr 2
  apply Subtype.ext
  exact rowQuotientAction_mk_apply F g x

/-- The 21-point source branch gives the full faithful natural row action
and a complement to the literal row subgroup in its ambient normalizer. -/
theorem row_structure [Finite G] (hcount : (F.fusion F.plane).ncard = 21) :
    Nonempty (rowQuotient F ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))) ∧
    Function.Bijective (rowQuotientAction F) ∧
    ∃ K : Subgroup (rowNormalizer F),
      (F.row.subgroupOf (rowNormalizer F)).IsComplement' K := by
  refine ⟨⟨rowQuotientEquiv F hcount⟩, ⟨rowQuotientAction_injective F, ?_⟩,
    row_normalizer_splits F⟩
  intro a
  obtain ⟨g, hg⟩ := row_action_surjective_of_normalizer_ne_centralizer F
    (row_normalizer_ne F hcount) a
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [← hg]
  ext x
  exact rowQuotientAction_mk_apply F g x

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
