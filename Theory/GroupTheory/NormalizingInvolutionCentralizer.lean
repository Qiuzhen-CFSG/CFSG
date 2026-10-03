module

public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Centralizers after adjoining a normalizing involution

If an involution v outside D normalizes D, its centralizer in D⟨v⟩
is the product of its centralizer in D and ⟨v⟩. The factors meet
trivially, so the centralizer order doubles. The proof uses the actual
multiplication decomposition of the join and preserves the natural lift
of v into that join. No ambient finiteness is required.

This is the elementary counting step used for the Hall-tail extension in
Janko–Thompson, Math. Z. 113 (1970), §4, p.392, Case 1.
-/

open Subgroup
open scoped Pointwise

/-- Adjoining an outside normalizing involution doubles its centralizer
order in the original subgroup. -/
public theorem Subgroup.card_centralizer_sup_zpowers_of_normalizing_involution
    {G : Type*} [Group G] (D : Subgroup G) (v : G)
    (hv : v ^ 2 = 1) (hout : v ∉ D) (hn : v ∈ normalizer (D : Set G)) :
    let L := D ⊔ zpowers v
    let vL : L := ⟨v, mem_sup_right (mem_zpowers v)⟩
    Nat.card (centralizer ({vL} : Set L)) =
      2 * Nat.card (D ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  intro L vL
  let C := centralizer ({v} : Set G)
  have hvC : v ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hwC : zpowers v ≤ C := zpowers_le.mpr hvC
  have heq : L ⊓ C = (D ⊓ C) ⊔ zpowers v := by
    apply le_antisymm
    · intro x hx
      have hxprod : x ∈ (D : Set G) * (zpowers v : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left D (zpowers v) (zpowers_le.mpr hn)]
        exact hx.1
      obtain ⟨d, hd, w, hw, rfl⟩ := hxprod
      have hdC : d ∈ C := by
        have hh := C.mul_mem hx.2 (C.inv_mem (hwC hw))
        simpa only [mul_inv_cancel_right] using hh
      exact mul_mem_sup ⟨hd, hdC⟩ hw
    · apply sup_le
      · exact inf_le_inf le_sup_left le_rfl
      · exact le_inf le_sup_right hwC
  have hmap : (centralizer ({vL} : Set L)).map L.subtype = L ⊓ C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
    · intro hx
      refine ⟨⟨x, hx.1⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
  rw [← card_map_of_injective L.subtype_injective, hmap, heq]
  apply card_sup_zpowers_of_normalizing_involution (D ⊓ C) v hv (fun h => hout h.1)
  apply centralizer_le_normalizer
  intro d hd
  exact mem_centralizer_singleton_iff.mp hd.2
