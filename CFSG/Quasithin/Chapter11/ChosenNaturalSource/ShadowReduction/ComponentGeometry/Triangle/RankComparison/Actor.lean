module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Inner
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Transport

/-!
# The literal reverse automizer as an inner G₂ actor

Coordinates on the same ambient subgroup A carry the U-conjugation image
into the full natural normalizer. The commutator rank computes its whole
moved-space dimension, and the centralizer kernel computes its image rank.
The small moved-space theorem removes field and scalar factors. The resulting
inner preimage is elementary, maps onto the actual U-action image, and retains
both rank four and moved dimension four.

This is the input to the remaining long-root placement in the mutual-action
contradiction, Aschbacher--Smith 11.4.1(2), printed p.776.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.G2
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
attribute [local instance] ZMod.algebra
variable {G F : Type*} [Group G] [Field F] [CharP F 2] [Finite F]

/-- The reverse automizer has a literal inner G₂ preimage with the same rank and movement. -/
theorem exists_inner_actor (hF : Nat.card F = 4)
    (A U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUA : U ≤ normalizer (A : Set G))
    (e : A ≃* Multiplicative (Natural.Space F))
    (β : normalizer (A : Set G) →* linearNormalizer (Natural.Normalizer.binary F))
    (hact : ∀ (n : normalizer (A : Set G)) (a : A),
      (e ⟨n.val * a.val * n.val⁻¹,
        (mem_normalizer_iff.mp n.property a.val).mp a.property⟩).toAdd =
        normalizerRepresentation (Natural.Normalizer.binary F) (β n) (e a).toAdd)
    (hcomm : rank (⁅U,A⁆ : Subgroup G) = 4)
    (hrank : rank (ChapterE.inducedAutomizer A U) = 4) :
    ∃ C : Subgroup (Model F), IsElementaryAbelian 2 C ∧
      C.map (normalizerEmbedding (Natural.Normalizer.binary F)) =
        (β.comp (inclusion hUA)).range ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator (Natural.Normalizer.binary F) ⊤ C) = 4 ∧ rank C = 4 := by
  let σ := normalizerRepresentation (Natural.Normalizer.binary F)
  let δ := β.comp (inclusion hUA)
  let j : Multiplicative (Natural.Space F) →* G := A.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := A.subtype_injective.comp e.symm.injective
  have hjr : j.range = A := by
    change (A.subtype.comp e.symm.toMonoidHom).range = A
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, A.range_subtype]
  have hδ (u : U) (v : Natural.Space F) : j (Multiplicative.ofAdd (σ (δ u) v)) =
      u.val * j (Multiplicative.ofAdd v) * u.val⁻¹ := by
    have hh := hact (inclusion hUA u) (e.symm (Multiplicative.ofAdd v))
    simp only [e.apply_symm_apply,toAdd_ofAdd] at hh
    have he := congrArg (fun w => (e.symm (Multiplicative.ofAdd w)).val) hh
    simpa only [ofAdd_toAdd,e.symm_apply_apply,coe_inclusion, j, σ, δ,
      MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,Subgroup.coe_subtype] using he.symm
  have hm : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ δ.range) = 4 := by
    have hc := embeddedSpace_card j hj (subspaceCommutator σ ⊤ δ.range)
    rw [embedded_moved σ A U j hjr δ hδ] at hc
    have hr : rank (⁅A,U⁆ : Subgroup G) =
        Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ δ.range) := by
      rw [rank,hc,Nat.log_pow (by decide : 1 < 2)]
    rw [commutator_comm] at hr
    exact hr.symm.trans hcomm
  have hr : rank δ.range = 4 :=
    (marked_action_rank σ (normalizerRepresentation_injective _) A U hUA j hj hjr δ hδ).trans hrank
  let : IsElementaryAbelian 2 δ.range :=
    IsElementaryAbelian.of_surjective δ.rangeRestrict δ.rangeRestrict_surjective
  refine ⟨δ.range.comap (normalizerEmbedding (Natural.Normalizer.binary F)),
    inner_preimage_elementary δ.range, ?_, ?_, ?_⟩
  · exact Subgroup.map_comap_eq_self (small_moved_le_inner hF δ.range hm.le)
  · rw [inner_preimage_moved hF δ.range hm.le]
    exact hm
  · exact (inner_preimage_rank hF δ.range hm.le).trans hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
