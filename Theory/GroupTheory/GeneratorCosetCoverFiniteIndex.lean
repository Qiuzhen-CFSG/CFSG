module

public import Theory.GroupTheory.GeneratorCosetCoverIndex

/-!
# Finite index from a finite generator coset cover

A finite family of representatives with certified signed transitions covers
the group by word induction. Inverting representatives gives a surjection onto
the left-coset quotient. Thus the quotient is finite even when the subgroup
itself is infinite, and its natural-number index is positive.

This supplements the cardinal upper bound in `GeneratorCosetCoverIndex`:
an upper bound alone would also hold for an infinite quotient, whose
natural-number cardinality is zero.

Source: the elementary coset-cover argument underlying Todd–Coxeter
enumeration, Todd and Coxeter, Proc. Edinburgh Math. Soc. 5 (1936), 26–34.
-/

namespace Subgroup.GeneratorCosetCover
public section

/-- A finite certified cover proves finiteness of the coset quotient without
any finiteness assumption on the subgroup. -/
theorem finite_quotient {G α ι : Type*} [Group G]
    {H : Subgroup G} {g : α → G} [Finite ι]
    (C : Subgroup.GeneratorCosetCover H g ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤) : Finite (G ⧸ H) := by
  let f : ι → G ⧸ H := fun i => QuotientGroup.mk ((C.repr i)⁻¹)
  have hf : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨h, i, hi⟩ := C.covers hgen x⁻¹
      refine ⟨i, Quotient.sound ?_⟩
      apply QuotientGroup.leftRel_apply.mpr
      have hx : x = (C.repr i)⁻¹ * h.val⁻¹ := by
        simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv hi
      simpa only [inv_inv, hx, mul_inv_cancel_left] using H.inv_mem h.property
  exact Finite.of_surjective f hf

/-- Positivity records that the index of a finitely covered subgroup is finite. -/
theorem index_pos {G α ι : Type*} [Group G]
    {H : Subgroup G} {g : α → G} [Finite ι]
    (C : Subgroup.GeneratorCosetCover H g ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤) : 0 < H.index := by
  have : Finite (G ⧸ H) := C.finite_quotient hgen
  exact Nat.card_pos

end
end Subgroup.GeneratorCosetCover
