module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRankOne
import Mathlib.Tactic.FinCases
/-!
# Full endpoint normalizers from the 21-element rectangle fusion sets

The rank-one locus has a unique eight-element additive subgroup containing
code 1: any point outside the first-row subspace has at most four common
rank-one additive neighbors with code 1. Hence a plane-normalizer element
sending the marked point (code 4) to code 1 preserves the actual row-plane
intersection. Source 39.6(4) then puts it in the row normalizer, where it
moves z. Source 39.3 now gives the full faithful natural four-space action
and the split extension. The opposite marking gives the column conclusion.

This derives the endpoint assertion of Aschbacher, *Sporadic Groups* (1994),
40.3 and the endpoint part of 40.5(1), pp.217–219, directly from the marked
21/21 fusion sets. The proof supplies the actual quotient isomorphism and
its conjugation formula, uses only 64-element local certificates, and never
assumes simplicity of the normalizer-generated subgroup. The rectangular
quotient identifications and the §41 source comparison remain obligations.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
namespace PlaneTensor
open PlaneCensus (Code pure)
open UniquenessMathieu.SourceNormalizer

private def rowCodes : Finset Code := Finset.univ.filter (fun x => x >>> 3 = 0)
private theorem rowCodes_card : rowCodes.card = 8 := by decide
private theorem rowCodes_zero : (0 : Code) ∈ rowCodes := by decide
private theorem rowCodes_point : (4 : Code) ∈ rowCodes := by decide
private theorem rowCodes_xor : ∀ x y : Code, x ∈ rowCodes → y ∈ rowCodes → x ^^^ y ∈ rowCodes := by decide
private theorem rowCodes_pure : ∀ x : Code, x ∈ rowCodes → x ≠ 0 → pure x = true := by decide
private def common (b : Code) : Finset Code := Finset.univ.filter (fun x =>
  (x = 0 ∨ pure x = true) ∧ (1 ^^^ x = 0 ∨ pure (1 ^^^ x) = true) ∧
    (b ^^^ x = 0 ∨ pure (b ^^^ x) = true))
private theorem common_bound : ∀ b : Code, b ∉ rowCodes →
    (b = 0 ∨ pure b = true) → (1 ^^^ b = 0 ∨ pure (1 ^^^ b) = true) →
      (common b).card ≤ 4 := by decide

private theorem eight_pure_eq_row (s : Finset Code) (hc : s.card = 8)
    (h1 : (1 : Code) ∈ s)
    (hp : ∀ a ∈ s, a = 0 ∨ pure a = true)
    (hadd : ∀ a ∈ s, ∀ b ∈ s, a ^^^ b ∈ s) : s = rowCodes := by
  have hle : s ⊆ rowCodes := by
    intro b hb
    by_contra hn
    have hsub : s ⊆ common b := by
      intro x hx
      simp only [common, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp x hx, hp _ (hadd 1 h1 x hx), hp _ (hadd b hb x hx)⟩
    have hcard := (Finset.card_le_card hsub).trans (common_bound b hn (hp b hb) (hp _ (hadd 1 h1 b hb)))
    omega
  exact Finset.eq_of_subset_of_card_le hle (by rw [hc, rowCodes_card])

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
private theorem element_mem_row_iff (x : Code) : element F x ∈ F.row ↔ x ∈ rowCodes := by
  have hc := F.pullback_le _ (element_mem F x)
  rw [F.mem_pullback_iff Model.row ⟨element F x, hc⟩, element_model, model_mem_row_iff]
  simpa only [rowCodes, Finset.mem_filter, Finset.mem_univ, true_and] using
    decode_secondRow_zero_iff x

private theorem action_preserves_pure [Finite G] (hlinear : F.LinearFusion)
    (n : normalizer (F.plane : Set G)) (x : Code) :
    pure (normalizerAction F n x) = true ↔ pure x = true := by
  rw [← fusion_iff_pure F hlinear, ← fusion_iff_pure F hlinear, normalizerAction_element]
  have he : IsConj (element F x) ((n : G) * element F x * (n : G)⁻¹) :=
    isConj_iff.mpr ⟨(n : G), rfl⟩
  exact ⟨fun h => h.trans he.symm, fun h => h.trans he⟩

private theorem action_zero (n : normalizer (F.plane : Set G)) :
    normalizerAction F n 0 = 0 := by
  apply element_injective F
  rw [normalizerAction_element, element_zero]
  simp

private theorem action_preserves_row [Finite G] (hlinear : F.LinearFusion)
    (n : normalizer (F.plane : Set G)) (hn : normalizerAction F n 4 = 1) :
    ∀ x ∈ rowCodes, normalizerAction F n x ∈ rowCodes := by
  classical
  let f := normalizerAction F n
  let s := rowCodes.image f
  have he : s = rowCodes := by
    apply eight_pure_eq_row
    · rw [Finset.card_image_of_injective _ f.injective, rowCodes_card]
    · exact Finset.mem_image.mpr ⟨4, rowCodes_point, hn⟩
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      by_cases hz : x = 0
      · left; subst x; exact action_zero F n
      · right
        exact (action_preserves_pure F hlinear n x).mpr (rowCodes_pure x hx hz)
    · intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨x ^^^ y, rowCodes_xor x y hx hy, normalizerAction_xor F n x y⟩
  intro x hx
  rw [← he]
  exact Finset.mem_image_of_mem f hx

/-- The 21-element branch provides a point-moving element preserving the
literal row-plane intersection. This is the missing movement used in 40.3. -/
theorem exists_row_plane_point_mover [Finite G] (hlinear : F.LinearFusion) :
    ∃ n ∈ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G), n * z * n⁻¹ ≠ z := by
  obtain ⟨n, hn, he⟩ := source_plane_fusion F (point_mem_plane F) (element_mem F 1)
    ((fusion_iff_pure F hlinear 1).mpr (by decide))
  have hm : normalizerAction F ⟨n, hn⟩ 4 = 1 := by
    apply element_injective F
    rw [normalizerAction_element, element_point]
    exact he
  refine ⟨n, ?_, he ▸ element_one_ne_point F⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha.2⟩
    have hxe : element F x = a := congrArg Subtype.val hx
    have hrow : x ∈ rowCodes := (element_mem_row_iff F x).mp (hxe.symm ▸ ha.1)
    have hh := action_preserves_row F hlinear ⟨n, hn⟩ hm x hrow
    have hmem := (element_mem_row_iff F _).mpr hh
    rw [normalizerAction_element, hxe] at hmem
    exact ⟨hmem, (mem_normalizer_iff.mp hn a).mp ha.2⟩
  · rw [card_map_of_injective (MulAut.conj n).injective]

end PlaneTensor
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The 21/21 branch excludes the point-centralizer alternative for the
actual row normalizer, as required by source 40.3. -/
theorem linear_rowNormalizer_ne_centralizer (hlinear : F.LinearFusion) :
    rowNormalizer F ≠ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨n, hn, hmove⟩ := PlaneTensor.exists_row_plane_point_mover F hlinear
  rw [source_row_plane_normalizer] at hn
  intro he
  have hc : n ∈ Subgroup.centralizer ({z} : Set G) := he ▸ hn.1
  exact hmove (by rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right])

/-- The literal row quotient has full binary four-space action in the
linear branch; its map is the previously constructed conjugation quotient. -/
def linearRowQuotientEquiv (hlinear : F.LinearFusion) :
    rowQuotient F ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
  (MulEquiv.ofBijective (rowQuotientAction F) ⟨rowQuotientAction_injective F, by
    intro a
    obtain ⟨g, hg⟩ := row_action_surjective_of_normalizer_ne_centralizer F
      (linear_rowNormalizer_ne_centralizer F hlinear) a
    refine ⟨QuotientGroup.mk g, ?_⟩
    rw [← hg]
    ext x
    exact rowQuotientAction_mk_apply F g x⟩).trans (rowAutLinearEquiv F)

/-- The natural-action identity retains the literal quotient map and the
original marked row coordinates. -/
theorem linearRowQuotientEquiv_action (hlinear : F.LinearFusion)
    (g : rowNormalizer F) (x : F.row) :
    linearRowQuotientEquiv F hlinear (QuotientGroup.mk g) (rowCoordinates F x).toAdd =
      (rowCoordinates F (F.row.normalizerMonoidHom g x)).toAdd := by
  change rowAutLinearEquiv F (rowQuotientAction F (QuotientGroup.mk g))
    (rowCoordinates F x).toAdd = _
  rw [rowAutLinearEquiv_apply]
  congr 2
  apply Subtype.ext
  exact rowQuotientAction_mk_apply F g x

/-- The other full normalizer action follows through the same opposite marking. -/
theorem linear_columnNormalizer_ne_centralizer (hlinear : F.LinearFusion) :
    columnNormalizer F ≠ Subgroup.centralizer ({z} : Set G) := by
  simpa only [rowNormalizer, columnNormalizer, oppositeMarking_row] using
    linear_rowNormalizer_ne_centralizer (oppositeMarking F) (oppositeMarking_linearFusion F hlinear)

/-- Both source endpoint normalizers have full natural action and split
extensions, with relative normality inherited from the actual normalizers. -/
theorem linear_endpoint_normalizers (hlinear : F.LinearFusion) :
    Function.Surjective F.row.normalizerMonoidHom ∧
    Function.Surjective F.column.normalizerMonoidHom ∧
    (∃ K : Subgroup (rowNormalizer F), (F.row.subgroupOf (rowNormalizer F)).IsComplement' K) ∧
    (∃ K : Subgroup (columnNormalizer F), (F.column.subgroupOf (columnNormalizer F)).IsComplement' K) :=
  ⟨row_action_surjective_of_normalizer_ne_centralizer F (linear_rowNormalizer_ne_centralizer F hlinear),
    column_action_surjective_of_normalizer_ne_centralizer F (linear_columnNormalizer_ne_centralizer F hlinear),
    row_normalizer_splits F, column_normalizer_splits F⟩

/-- The point centralizer has relative index fifteen in each of the original
endpoint normalizers. These are the actual source intersections. -/
theorem linear_endpoint_point_indices (hlinear : F.LinearFusion) :
    (Subgroup.centralizer ({z} : Set G)).relIndex (rowNormalizer F) = 15 ∧
    (Subgroup.centralizer ({z} : Set G)).relIndex (columnNormalizer F) = 15 := by
  refine ⟨point_centralizer_row_index F (linear_rowNormalizer_ne_centralizer F hlinear), ?_⟩
  simpa only [rowNormalizer, columnNormalizer, oppositeMarking_row] using
    point_centralizer_row_index (oppositeMarking F)
      (linear_rowNormalizer_ne_centralizer (oppositeMarking F) (oppositeMarking_linearFusion F hlinear))

/-- The 41.1 induction subgroup retains the full row action and splitting.
This application uses its inherited fusion counts, never a simplicity premise. -/
theorem normalizerSpan_full_row_action (hlinear : F.LinearFusion) :
    Function.Surjective (normalizerSpanMarking F).row.normalizerMonoidHom ∧
      ∃ K : Subgroup (rowNormalizer (normalizerSpanMarking F)),
        ((normalizerSpanMarking F).row.subgroupOf
          (rowNormalizer (normalizerSpanMarking F))).IsComplement' K := by
  have h := linear_endpoint_normalizers (normalizerSpanMarking F) (normalizerSpan_linearFusion F hlinear)
  exact ⟨h.1, h.2.2.1⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
