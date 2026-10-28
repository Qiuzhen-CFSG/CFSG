module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.Basic
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupAction.ExtraspecialThirtyTwoCubic
public import Theory.GroupTheory.QuaternionCentralProductFactorNormality

/-!
# Local structure of the involution centralizer in I.4.6

The source core is the actual two-core, the centralizer has order 192, its
Sylow three-subgroup has order three, and its Sylow two-subgroups have order 64.
The core center is the distinguished involution line. This characteristic
center proves that the core's ambient normalizer is exactly the centralizer;
the source fusion then makes both proper in the required sense.

The key local step restricts the literal conjugation action to the chosen
Sylow three-subgroup. The source equality `C_Q(X) = ⟨z⟩` identifies its fixed
subgroup with `Z(Q)`. Orbit counting excludes the minus type and constructs
the quaternion–quaternion central product. Its factors are precisely the two
quaternion subgroups, and their normality in the centralizer is simultaneous.
No simplicity, sign, global recognition, or model order is assumed here.

Source: Aschbacher–Smith, I.4.6, combined manuscript of 1 March 2004,
printed p.417, `refs/quasithin.pdf`; Aschbacher, “A 2-local characterization
of M12”, Illinois J. Math. 47 (2003), 31–47.
-/

namespace CFSG.Quasithin.Extraspecial32
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {z : G}

public theorem coreInG_le (z : G) : coreInG z ≤ Centralizer z := map_subtype_le _

public theorem coreInG_subgroupOf (z : G) :
    (coreInG z).subgroupOf (Centralizer z) = Core z :=
  comap_map_eq_self_of_injective (Centralizer z).subtype_injective _

namespace Hypotheses
variable [Finite G]

public theorem distinguished_order (h : Hypotheses z) : orderOf (distinguished z) = 2 :=
  (Subgroup.orderOf_coe (distinguished z)).symm.trans h.involution

public theorem distinguished_mem_core (h : Hypotheses z) : distinguished z ∈ Core z := by
  have hz := mem_zpowers (distinguished z)
  rw [← h.fixed] at hz
  exact hz.1

public theorem core_eq_pCore (h : Hypotheses z) : Core z = pCore 2 (Centralizer z) := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, IsPGroup.of_card (p := 2) (n := 5) h.core_card⟩
  · exact (pCore_le_fitting (Centralizer z) 2).trans (fitting_le_generalizedFitting _)

public theorem quotient_card (h : Hypotheses z) : Nat.card (Centralizer z ⧸ Core z) = 6 := by
  rw [Nat.card_congr h.quotient_model.some.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  decide

public theorem centralizer_card (h : Hypotheses z) : Nat.card (Centralizer z) = 192 := by
  rw [card_eq_card_quotient_mul_card_subgroup (Core z), h.quotient_card, h.core_card]

public theorem sylow_three_card (h : Hypotheses z) : Nat.card h.X = 3 := by
  rw [h.X.card_eq_multiplicity, h.centralizer_card]
  decide +kernel

public theorem centralizer_sylow_two_card (h : Hypotheses z)
    (S : Sylow 2 (Centralizer z)) : Nat.card S = 64 := by
  rw [S.card_eq_multiplicity, h.centralizer_card]
  decide +kernel

public theorem core_center_image (h : Hypotheses z) :
    (center (Core z)).map (Core z).subtype = zpowers (distinguished z) := by
  let : IsExtraspecial 2 (Core z) := h.extraspecial
  have hzZ : (⟨distinguished z, h.distinguished_mem_core⟩ : Core z) ∈ center (Core z) := by
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp q.val.property
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem _ hzZ)) ?_).symm
  rw [card_map_of_injective (Core z).subtype_injective,
    IsExtraspecial.center_order_p 2 (Core z), Nat.card_zpowers]
  exact h.distinguished_order.ge

public theorem coreInG_card (h : Hypotheses z) : Nat.card (coreInG z) = 32 := by
  rw [coreInG, card_map_of_injective (Centralizer z).subtype_injective, h.core_card]

public theorem involution_mem_coreInG (h : Hypotheses z) : z ∈ coreInG z :=
  mem_map_of_mem (Centralizer z).subtype h.distinguished_mem_core

public theorem coreInG_extraspecial (h : Hypotheses z) : IsExtraspecial 2 (coreInG z) :=
  IsExtraspecial.of_mulEquiv
    ((Core z).equivMapOfInjective _ (Centralizer z).subtype_injective) h.extraspecial

public theorem coreInG_center_image (h : Hypotheses z) :
    (center (coreInG z)).map (coreInG z).subtype = zpowers z := by
  let := h.coreInG_extraspecial
  have hzZ : (⟨z, h.involution_mem_coreInG⟩ : coreInG z) ∈ center (coreInG z) := by
    exact mem_center_iff.mpr fun q =>
      Subtype.ext (mem_centralizer_singleton_iff.mp (coreInG_le z q.property))
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem _ hzZ)) ?_).symm
  rw [card_map_of_injective (coreInG z).subtype_injective,
    IsExtraspecial.center_order_p 2 (coreInG z), Nat.card_zpowers]
  exact h.involution.ge

public theorem normalizer_core (h : Hypotheses z) : normalizer (coreInG z : Set G) = Centralizer z := by
  apply le_antisymm
  · exact normalizer_le_centralizer_of_characteristic_involution
      (coreInG z) (center (coreInG z)) z h.involution h.coreInG_center_image
  · apply (normal_subgroupOf_iff_le_normalizer (coreInG_le z)).mp
    rw [coreInG_subgroupOf]
    infer_instance

public theorem exists_conjugator_outside (h : Hypotheses z) :
    ∃ g : G, g ∉ Centralizer z ∧ g * z * g⁻¹ ∈ coreInG z := by
  obtain ⟨g, hgQ, hg⟩ := h.fused
  refine ⟨g, ?_, hgQ⟩
  intro hgH
  exact hg (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgH))

public theorem centralizer_ne_top (h : Hypotheses z) : Centralizer z ≠ ⊤ := by
  obtain ⟨g, hg, _⟩ := h.exists_conjugator_outside
  intro he
  exact hg (he ▸ mem_top g)

public theorem coreInG_not_normal (h : Hypotheses z) : ¬ (coreInG z).Normal := by
  intro hn
  exact h.centralizer_ne_top (h.normalizer_core.symm.trans (normalizer_eq_top_iff.mpr hn))

public theorem quaternionCentralProduct (h : Hypotheses z) :
    Nonempty (QuaternionCentralProductData (Core z)) := by
  let : IsExtraspecial 2 (Core z) := h.extraspecial
  let action : h.X →* MulAut (Core z) :=
    MulAut.conjNormal.comp (h.X : Subgroup (Centralizer z)).subtype
  let : MulDistribMulAction h.X (Core z) := MulDistribMulAction.compHom _ action
  apply Theory.GroupAction.quaternionCentralProduct_of_three_fixed_center h.X.isPGroup' h.core_card
  intro u
  have hfix : (∀ a : h.X, a • u = u) ↔
      (u : Centralizer z) ∈ centralizer (h.X : Set (Centralizer z)) := by
    constructor
    · intro hu x hx
      have he := congrArg (fun q : Core z => (q : Centralizer z)) (hu ⟨x, hx⟩)
      change x * (u : Centralizer z) * x⁻¹ = u at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hu a
      apply Subtype.ext
      change (a : Centralizer z) * (u : Centralizer z) * (a : Centralizer z)⁻¹ = u
      exact mul_inv_eq_iff_eq_mul.mpr (hu a a.property)
  refine hfix.trans ?_
  constructor
  · intro hu
    have hline : (u : Centralizer z) ∈ zpowers (distinguished z) :=
      h.fixed ▸ (show (u : Centralizer z) ∈ Core z ⊓ centralizer (h.X : Set (Centralizer z))
        from ⟨u.property, hu⟩)
    rw [← h.core_center_image] at hline
    obtain ⟨v, hv, he⟩ := hline
    exact (Subtype.ext he : v = u) ▸ hv
  · intro hu
    have hline : (u : Centralizer z) ∈ zpowers (distinguished z) :=
      h.core_center_image ▸ mem_map_of_mem (Core z).subtype hu
    rw [← h.fixed] at hline
    exact hline.2

public theorem quaternion_subgroups_card (h : Hypotheses z) :
    Nat.card {R : Subgroup (Core z) // Nonempty (R ≃* QuaternionGroup 2)} = 2 := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  exact d.quaternion_subgroups_card

public theorem quaternion_normality_dichotomy (h : Hypotheses z) :
    QuaternionSubgroupsNormal z ∨ QuaternionSubgroupsNonnormal z := by
  classical
  obtain ⟨d⟩ := h.quaternionCentralProduct
  have hn := QuaternionCentralProductData.normal_left_iff_normal_right (Core z) d
  by_cases hl : (d.left.map (Core z).subtype).Normal
  · left
    intro R hR
    rcases (d.quaternion_subgroup_iff R).mp hR with rfl | rfl
    · exact hl
    · exact hn.mp hl
  · right
    intro R hR
    rcases (d.quaternion_subgroup_iff R).mp hR with rfl | rfl
    · exact hl
    · exact fun hr => hl (hn.mpr hr)

public theorem quaternion_normality_exclusive (h : Hypotheses z) :
    ¬ (QuaternionSubgroupsNormal z ∧ QuaternionSubgroupsNonnormal z) := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  rintro ⟨hn, hnn⟩
  exact hnn d.left d.left_model (hn d.left d.left_model)

end Hypotheses
end CFSG.Quasithin.Extraspecial32
