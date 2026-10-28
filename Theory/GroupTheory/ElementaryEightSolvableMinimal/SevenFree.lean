module

public import Theory.GroupTheory.ElementaryEightSolvableMinimal

/-!
# The seven-free ambient form of the elementary-eight obstruction

The automizer argument only needs seven to be absent from the ambient group
order. This transports that proved obstruction through the actual conjugation
map of a normal subgroup. It also applies to the intrinsic Janko-four
{2,11} pair, retaining the same canonical central closure and minimality.
-/

public section
noncomputable section
open Subgroup

/-- A finite solvable group of order prime to seven has no minimal normal
elementary abelian subgroup of order eight. -/
theorem not_minimal_normal_elementary_eight_of_solvable_seven_free
    {H : Type*} [Group H] [Finite H] (E : Subgroup H) [E.Normal]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) (hs : Group.IsSolvable H)
    (hseven : ¬ 7 ∣ Nat.card H)
    (hmin : ∀ B : Subgroup H, B ≤ E → B.Normal → B = ⊥ ∨ B = E) : False := by
  let f : H →* MulAut E := MulAut.conjNormal
  let A := f.range
  let : Group.IsSolvable H := hs
  let : Group.IsSolvable A := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hsevenA : ¬ 7 ∣ Nat.card A := fun hh => hseven (hh.trans (card_range_dvd f))
  apply not_irreducible_solvable_elementary_eight hE A hsevenA
  intro D hD
  have hn : (D.map E.subtype).Normal := by
    constructor
    rintro x ⟨x, hx, rfl⟩ h
    exact ⟨f h x, hD ⟨f h, ⟨h, rfl⟩⟩ x hx, rfl⟩
  rcases hmin (D.map E.subtype) (map_subtype_le D) hn with hh | hh
  · exact Or.inl ((D.map_eq_bot_iff_of_injective E.subtype_injective).mp hh)
  · apply Or.inr
    apply Subgroup.map_injective E.subtype_injective
    rw [hh, ← MonoidHom.range_eq_map, E.range_subtype]
