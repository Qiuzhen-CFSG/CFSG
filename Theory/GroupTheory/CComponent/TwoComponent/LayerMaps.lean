module

public import Theory.GroupTheory.CComponent.TwoComponent.OddQuotient

/-!
# Maps of two-layers

Two-layers commute with group isomorphisms. Factoring a surjection through
its literal kernel quotient therefore extends the odd normal quotient
correspondence to arbitrary surjections with odd solvable kernel.

Source: GLS II, Proposition 4.7(iii), in the form used by 5.19(iii).
-/

@[expose] public section
open Subgroup
namespace Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- Two-layers are preserved by group isomorphisms. -/
theorem map_twoComponentLayer_equiv (e : G ≃* H) :
    (twoComponentLayer G).map e.toMonoidHom = twoComponentLayer H := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    exact sSup_le fun L hL => map_le_iff_le_comap.mp
      (hL.map_equiv e).le_twoComponentLayer
  · refine sSup_le fun L hL => ?_
    have h := map_mono (f := e.toMonoidHom) (hL.map_equiv e.symm).le_twoComponentLayer
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext x
      exact e.apply_symm_apply x
    simpa only [map_map, he, map_id] using h

variable [Finite G]

/-- The odd normal quotient correspondence applies to every odd-kernel surjection. -/
theorem map_twoComponentLayer_of_surjective_odd_kernel
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hk : Odd (Nat.card f.ker)) :
    (twoComponentLayer G).map f = twoComponentLayer H := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : e.toMonoidHom.comp (QuotientGroup.mk' f.ker) = f := rfl
  rw [← he, ← map_map, map_twoComponentLayer_odd_quotient f.ker hk,
    map_twoComponentLayer_equiv]

end Subgroup
