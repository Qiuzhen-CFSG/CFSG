module
public import Theory.GroupTheory.CComponent.BinaryRankTwo

/-!
# Marking the actual two-core image of a component

The intrinsic quotient of a C-component identifies with its image in the
ambient two-core quotient. The constructed embedding retains the prescribed
model coordinates on every original component element. When the component is
the solvable residual and the solvable radical is the two-core, that image is
normal and has trivial centralizer: the radical-free layer already lies in it.

Source: Aschbacher--Smith, A.3.3 and original 14.6.21(1), pp.42--43,1037.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {H S : Type*} [Group H] [Finite H] [Group S]

/-- Embed the prescribed intrinsic quotient as the literal ambient image. -/
theorem exists_twoCore_component_marking
    (K : Subgroup H) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* S) :
    ∃ κ : S →* H ⧸ pCore 2 H, Function.Injective κ ∧
      κ.range = K.map (QuotientGroup.mk' (pCore 2 H)) ∧
      ∀ k : K, κ (e (QuotientGroup.mk' (pCore 2 K) k)) =
        QuotientGroup.mk' (pCore 2 H) k := by
  let a := cComponentTwoCoreQuotientEquiv hK
  let b := e.symm.trans a
  let κ := (K.map (QuotientGroup.mk' (pCore 2 H))).subtype.comp b.toMonoidHom
  refine ⟨κ, Subtype.val_injective.comp b.injective, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr b.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  · intro k
    change ((a (e.symm (e (QuotientGroup.mk' _ k))) :
      K.map (QuotientGroup.mk' (pCore 2 H))) : H ⧸ pCore 2 H) = _
    rw [e.symm_apply_apply]
    rfl

/-- The marked residual image is normal and self-centralizing modulo O₂. -/
theorem residual_component_marking_properties
    (hR : solvableRadical H = pCore 2 H)
    (K : Subgroup H) (hres : solvableResidual H = K)
    (κ : S →* H ⧸ pCore 2 H)
    (hr : κ.range = K.map (QuotientGroup.mk' (pCore 2 H))) :
    κ.range.Normal ∧ centralizer (κ.range : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have he : K.map q = solvableResidual (H ⧸ pCore 2 H) := by
    rw [←hres, map_solvableResidual_eq q (QuotientGroup.mk'_surjective _)]
  have hn : κ.range.Normal := by rw [hr, he]; infer_instance
  have hQ : solvableRadical (H ⧸ pCore 2 H) = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq hR)
    rw [solvableRadical_quotient_solvableRadical, Subgroup.map_bot] at hh
    exact hh.symm
  have hl : cComponentLayer (H ⧸ pCore 2 H) ≤ K.map q := by
    rw [he]
    let := cComponentLayer_isPerfect (G := H ⧸ pCore 2 H)
    exact le_solvableResidual_of_isPerfect _
  refine ⟨hn, le_bot_iff.mp ?_⟩
  rw [hr]
  exact (centralizer_le hl).trans
    (centralizer_cComponentLayer_eq_bot_of_radical_eq_bot hQ).le
end Subgroup
