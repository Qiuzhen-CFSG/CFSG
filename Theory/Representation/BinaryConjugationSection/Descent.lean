module

public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# Descent of literal binary section actions

A surjective actor map acts on the actual section L/Z whenever its kernel
centralizes L/Z. Only kernel containment is needed; the descended action
need not be faithful. Coordinates retain the literal quotient map.

This is the action descent used for the binary PSL₃ row of E.2.17.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Representation.BinaryConjugationSection
variable {G D : Type*} [Group G] [Group D]

theorem exists_descended_actor
    (H L Z : Subgroup G) (hLH : L ≤ H) (hZL : Z ≤ L)
    (hNL : H ≤ normalizer (L : Set G)) (hNZ : H ≤ normalizer (Z : Set G))
    [(Z.subgroupOf L).Normal] [IsElementaryAbelian 2 (L ⧸ Z.subgroupOf L)]
    (π : H →* D) (hπ : Function.Surjective π)
    (hk : ∀ a : H, π a = 1 → ∀ l ∈ L, ⁅(a : G), l⁆ ∈ Z) :
    ∃ (σ : Representation (ZMod 2) D (Additive (L ⧸ Z.subgroupOf L)))
      (c : BinaryConjugationSection H L Z (σ.comp π)),
      ∀ l : L, (c.coordinates l).toAdd =
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf L) l) := by
  let Q := L ⧸ Z.subgroupOf L
  let q := QuotientGroup.mk' (Z.subgroupOf L)
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action H L Z hNL hNZ inferInstance
  have hkill : π.ker ≤ α.ker := by
    intro a ha
    apply MulEquiv.ext
    intro w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf L) w
    rw [hα]
    change q _ = q l
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (a : G) * (l : G) * (a : G)⁻¹ / (l : G) ∈ Z
    simpa only [div_eq_mul_inv, commutatorElement_def] using hk a ha l l.property
  let β : D →* MulAut Q := π.liftOfSurjective hπ ⟨α, hkill⟩
  have hβ (a : H) : β (π a) = α a :=
    π.liftOfRightInverse_comp_apply (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨α, hkill⟩ a
  let σ : Representation (ZMod 2) D (Additive Q) := {
    toFun a := (β a).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by ext v; change β 1 v.toMul = v.toMul; rw [map_one]; rfl
    map_mul' a b := by
      ext v
      change β (a*b) v.toMul = β a (β b v.toMul)
      rw [map_mul]
      rfl }
  let cL : L →* Multiplicative (Additive Q) := {
    toFun l := Multiplicative.ofAdd (Additive.ofMul (q l))
    map_one' := q.map_one
    map_mul' := q.map_mul }
  let c : BinaryConjugationSection H L Z (σ.comp π) := {
    section_le := hLH
    kernel_le := hZL
    normalized := hNL
    coordinates := cL
    onto := QuotientGroup.mk'_surjective _
    kernel_eq := QuotientGroup.ker_mk' _
    equivariant := by
      intro a l
      change q _ = β (π a) (q l)
      rw [hβ]
      exact (hα a l).symm }
  exact ⟨σ, c, fun _ => rfl⟩

end Representation.BinaryConjugationSection
