module

public import CFSG.Quasithin.ChapterE.Defs

/-!
# Minimal supplements: existence and subgroup identities

Finiteness supplies the minimal supplements of Definition E.1.9. The subgroup
identities in E.1.10(1) only use the supplement and containment conditions,
not minimality. They follow by writing an element of a join with a normal
subgroup as a product and cancelling the factor already in the smaller group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.9 and E.1.10(1), p.211.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The source family of minimal supplements is nonempty. -/
theorem exists_minimalSupplement (T X Y : Subgroup G) (hYX : Y ≤ X) :
    ∃ K : Subgroup G, IsMinimalSupplement T X Y K := by
  apply exists_minimal_of_wellFoundedLT
  refine ⟨X ⊔ T, le_sup_right, le_rfl, ?_⟩
  exact sup_eq_left.mpr (hYX.trans le_sup_left)

omit [Finite G] in
/-- The first subgroup equality in E.1.10(1). -/
theorem IsMinimalSupplement.eq_inf_sup {T X Y K : Subgroup G} [X.Normal]
    (h : IsMinimalSupplement T X Y K) : K = (K ⊓ X) ⊔ T := by
  apply le_antisymm
  · intro k hk
    have hm : k ∈ T ⊔ X := sup_comm X T ▸ h.1.2.1 hk
    obtain ⟨t, ht, x, hx, rfl⟩ := mem_sup_of_normal_right.mp hm
    have hxK : x ∈ K := (K.mul_mem_cancel_left (h.1.1 ht)).mp hk
    exact ((K ⊓ X) ⊔ T).mul_mem ((show T ≤ (K ⊓ X) ⊔ T from le_sup_right) ht)
      ((show K ⊓ X ≤ (K ⊓ X) ⊔ T from le_sup_left) ⟨hxK, hx⟩)
  · exact sup_le inf_le_left h.1.1

omit [Finite G] in
/-- The kernel supplement identity used for the isomorphisms in E.1.10(1). -/
theorem IsMinimalSupplement.inf_sup_kernel {T X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement T X Y K) (hYX : Y ≤ X) :
    (K ⊓ X) ⊔ Y = X := by
  apply le_antisymm (sup_le inf_le_right hYX)
  intro x hx
  have hm : x ∈ K ⊔ Y := h.1.2.2.symm ▸ (show X ≤ X ⊔ T from le_sup_left) hx
  obtain ⟨k, hk, y, hy, rfl⟩ := mem_sup_of_normal_right.mp hm
  have hkX : k ∈ X := (X.mul_mem_cancel_right (hYX hy)).mp hx
  exact ((K ⊓ X) ⊔ Y).mul_mem ((show K ⊓ X ≤ (K ⊓ X) ⊔ Y from le_sup_left) ⟨hk, hkX⟩)
    ((show Y ≤ (K ⊓ X) ⊔ Y from le_sup_right) hy)

omit [Finite G] in
/-- E.1.10(1): the genuine isomorphism `X/Y ≃ KX/KY`.
Here `Y.subgroupOf (K ⊓ X)` is `KY` inside `KX`, since `Y ≤ X`. -/
noncomputable def IsMinimalSupplement.quotientEquiv {T X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement T X Y K) (hYX : Y ≤ X) :
    X ⧸ Y.subgroupOf X ≃* (K ⊓ X : Subgroup G) ⧸ Y.subgroupOf (K ⊓ X) :=
  ((QuotientGroup.quotientInfEquivProdNormalQuotient (K ⊓ X) Y).trans
    (QuotientGroup.equivQuotientSubgroupOfOfEq rfl (h.inf_sup_kernel hYX))).symm

omit [Finite G] in
/-- E.1.10(1): the images of `X` and `KX` in `G/Y` coincide. -/
theorem IsMinimalSupplement.map_inf_eq {T X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement T X Y K) (hYX : Y ≤ X) :
    (K ⊓ X).map (QuotientGroup.mk' Y) = X.map (QuotientGroup.mk' Y) := by
  have he := congrArg (fun U : Subgroup G => U.map (QuotientGroup.mk' Y))
    (h.inf_sup_kernel hYX)
  simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] using he

omit [Finite G] in
/-- E.1.10(1): `X/Y` is isomorphic to the actual image of `KX` in `G/Y`. -/
noncomputable def IsMinimalSupplement.quotientImageEquiv {T X Y K : Subgroup G}
    [Y.Normal] (h : IsMinimalSupplement T X Y K) (hYX : Y ≤ X) :
    X ⧸ Y.subgroupOf X ≃* (K ⊓ X).map (QuotientGroup.mk' Y) := by
  let f := (QuotientGroup.mk' Y).subgroupMap (K ⊓ X)
  have hk : Y.subgroupOf (K ⊓ X) = f.ker := by
    ext x
    change (x : G) ∈ Y ↔ f x = 1
    rw [Subtype.ext_iff]
    exact (QuotientGroup.eq_one_iff (x : G)).symm
  exact (h.quotientEquiv hYX).trans ((QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' Y).subgroupMap_surjective (K ⊓ X))))

end CFSG.Quasithin.ChapterE
