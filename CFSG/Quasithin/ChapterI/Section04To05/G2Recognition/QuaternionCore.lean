module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.LocalStructure

/-!
# The quaternion subgroup in the G₂(3) recognition centralizer

The two marked normal SL₂(3) factors have quaternion two-cores. Their
intersection is the original common central involution: that line is a
normal two-subgroup of each factor. Their product is therefore Q₈ * Q₈,
normal in H, of order 32 and index 18. Its center is exactly the original
intersection, with the actual subgroup inclusions retained.

This constructs the subgroup Q₁Q₂ in Fong–Wong, Nagoya Math. J. 36 (1969),
§2B, printed p.151, from Aschbacher–Smith (G1), printed p.417. It is used
by the local-to-ambient Sylow promotion in `SylowStructure.lean`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

/-- The product of the actual quaternion cores of the two marked factors. -/
def quaternionCore : Subgroup c.H := c.H₁.pCoreIn 2 ⊔ c.H₂.pCoreIn 2

noncomputable def factorCoreEquiv (I : Subgroup c.H)
    (e : I ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    I.pCoreIn 2 ≃* QuaternionGroup 2 :=
  ((pCore 2 I).equivMapOfInjective I.subtype I.subtype_injective).symm.trans
    (((pCore 2 I).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (pCore_map_iso 2 e)).trans
        GLS3.Chapter5.SchurPresentation.sl23_twoCoreEquiv))

omit [Finite G] in
private theorem intersection_le_factor_core (I J : Subgroup c.H) [J.Normal]
    (hc : Nat.card (I ⊓ J : Subgroup c.H) = 2) : I ⊓ J ≤ I.pCoreIn 2 := by
  have hcard : Nat.card (J.subgroupOf I) = 2 := by
    rw [← card_map_of_injective I.subtype_injective, subgroupOf_map_subtype, inf_comm]
    exact hc
  have hp : IsPGroup 2 (J.subgroupOf I) := IsPGroup.of_card (n := 1) hcard
  have hle : J.subgroupOf I ≤ pCore 2 I := le_sSup ⟨inferInstance, hp⟩
  intro x hx
  exact ⟨⟨x,hx.1⟩, hle hx.2, rfl⟩

omit [Finite G] in
theorem factor_core_intersection :
    c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2 = c.H₁ ⊓ c.H₂ := by
  apply le_antisymm (inf_le_inf (c.H₁.pCoreIn_le 2) (c.H₂.pCoreIn_le 2))
  exact le_inf (intersection_le_factor_core c c.H₁ c.H₂ (intersection_card c))
    (by simpa only [inf_comm] using
      intersection_le_factor_core c c.H₂ c.H₁ (by simpa only [inf_comm] using intersection_card c))

instance quaternionCore_normal : (quaternionCore c).Normal := by
  let : ((pCore 2 c.H₁).map c.H₁.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  let : ((pCore 2 c.H₂).map c.H₂.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  change (((pCore 2 c.H₁).map c.H₁.subtype) ⊔ ((pCore 2 c.H₂).map c.H₂.subtype)).Normal
  infer_instance

noncomputable def quaternionCoreData : QuaternionCentralProductData (quaternionCore c) where
  left := (c.H₁.pCoreIn 2).subgroupOf (quaternionCore c)
  right := (c.H₂.pCoreIn 2).subgroupOf (quaternionCore c)
  left_model := ⟨(subgroupOfEquivOfLe le_sup_left).trans (factorCoreEquiv c c.H₁ c.H₁_model.some)⟩
  right_model := ⟨(subgroupOfEquivOfLe le_sup_right).trans (factorCoreEquiv c c.H₂ c.H₂_model.some)⟩
  intersection_card := by
    change Nat.card ((c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2).subgroupOf (quaternionCore c)) = 2
    rw [Nat.card_congr (subgroupOfEquivOfLe (show c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2 ≤
      quaternionCore c from inf_le_left.trans le_sup_left)).toEquiv]
    rw [factor_core_intersection c, intersection_card c]
  commute := by
    intro b hb d hd
    exact Subtype.ext (c.commute b (c.H₁.pCoreIn_le 2 hb) d (c.H₂.pCoreIn_le 2 hd))
  span := by
    change (c.H₁.pCoreIn 2).subgroupOf (c.H₁.pCoreIn 2 ⊔ c.H₂.pCoreIn 2) ⊔
      (c.H₂.pCoreIn 2).subgroupOf (c.H₁.pCoreIn 2 ⊔ c.H₂.pCoreIn 2) = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self _

theorem quaternionCore_card : Nat.card (quaternionCore c) = 32 :=
  (quaternionCoreData c).card

theorem quaternionCore_index : (quaternionCore c).index = 18 := by
  have h := (quaternionCore c).card_mul_index
  rw [quaternionCore_card c, H_card c] at h
  omega

theorem quaternionCore_center :
    (center (quaternionCore c)).map (quaternionCore c).subtype = c.H₁ ⊓ c.H₂ := by
  rw [(quaternionCoreData c).center_eq]
  change (((c.H₁.pCoreIn 2).subgroupOf (quaternionCore c)) ⊓
    ((c.H₂.pCoreIn 2).subgroupOf (quaternionCore c))).map _ = _
  change ((c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2).subgroupOf (quaternionCore c)).map _ = _
  rw [map_subgroupOf_eq_of_le
    (show c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2 ≤ quaternionCore c from inf_le_left.trans le_sup_left),
    factor_core_intersection c]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
